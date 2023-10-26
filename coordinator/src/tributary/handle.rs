use core::{ops::Deref, future::Future};
use std::collections::HashMap;
use std::io::Read;
use zeroize::Zeroizing;

use ciphersuite::{group::GroupEncoding, Ciphersuite, Ristretto};
use frost::dkg::Participant;

use serai_client::{
  Signature,
  validator_sets::primitives::{ValidatorSet, KeyPair},
  subxt::utils::Encoded,
  SeraiValidatorSets,
};

use tributary::Signed;

use processor_messages::{
  key_gen::{self, KeyGenId},
  coordinator,
  sign::{self, SignId},
};

use serai_db::{Get, Db};

use crate::{
  processors::Processors,
  tributary::{
    Transaction, TributarySpec, Topic, DataSpecification,
    FatallySlashedDb,
    nonce_decider::NonceDecider,
    dkg_confirmer::DkgConfirmer,
    scanner::{RecognizedIdType, RIDTrait}, DataDb,
  },
};

use super::{PlanIdsDb, CurrentlyCompletingKeyPairDb, KeyPairDb, AttemptDb, DataReceivedDb};

const DKG_COMMITMENTS: &str = "commitments";
const DKG_SHARES: &str = "shares";
const DKG_CONFIRMATION_NONCES: &str = "confirmation_nonces";
const DKG_CONFIRMATION_SHARES: &str = "confirmation_shares";

// These s/b prefixes between Batch and Sign should be unnecessary, as Batch/Share entries
// themselves should already be domain separated
const BATCH_PREPROCESS: &str = "b_preprocess";
const BATCH_SHARE: &str = "b_share";

const SIGN_PREPROCESS: &str = "s_preprocess";
const SIGN_SHARE: &str = "s_share";

fn read_known_to_exist_data<G: Get>(
  getter: &G,
  spec: &TributarySpec,
  key: &Zeroizing<<Ristretto as Ciphersuite>::F>,
  data_spec: &DataSpecification,
  needed: u16,
) -> Option<HashMap<Participant, Vec<u8>>> {
  let mut data = HashMap::new();
  for validator in spec.validators().iter().map(|validator| validator.0) {
    if let Some(bytes) = DataDb::get(getter, data_spec.as_key(spec.genesis()).to_vec(), validator.to_bytes() as [u8; 32]) {
      data.insert(spec.i(validator).unwrap(), bytes);
    };
  }
  assert_eq!(data.len(), usize::from(needed));

  // Remove our own piece of data, if we were involved
  if data
    .remove(
      &spec
        .i(Ristretto::generator() * key.deref())
        .expect("handling a message for a Tributary we aren't part of"),
    )
    .is_some()
  {
    Some(data)
  } else {
    None
  }
}

pub fn dkg_confirmation_nonces(
  key: &Zeroizing<<Ristretto as Ciphersuite>::F>,
  spec: &TributarySpec,
  attempt: u32,
) -> [u8; 64] {
  DkgConfirmer::preprocess(spec, key, attempt)
}

#[allow(clippy::needless_pass_by_ref_mut)]
pub fn generated_key_pair<D: Db>(
  txn: &mut D::Transaction<'_>,
  key: &Zeroizing<<Ristretto as Ciphersuite>::F>,
  spec: &TributarySpec,
  key_pair: &KeyPair,
  attempt: u32,
) -> Result<[u8; 32], Participant> {
  CurrentlyCompletingKeyPairDb::set(txn, spec.genesis(), key_pair);

  let Some(preprocesses) = read_known_to_exist_data::<_>(
    txn,
    spec,
    key,
    &DataSpecification { topic: Topic::Dkg, label: DKG_CONFIRMATION_NONCES, attempt },
    spec.n(),
  ) else {
    panic!("wasn't a participant in confirming a key pair");
  };
  DkgConfirmer::share(spec, key, attempt, preprocesses, key_pair)
}

pub(crate) fn fatal_slash<D: Db>(
  txn: &mut D::Transaction<'_>,
  genesis: [u8; 32],
  account: [u8; 32],
  reason: &str,
) {
  log::warn!("fatally slashing {}. reason: {}", hex::encode(account), reason);
  FatallySlashedDb::set_fatally_slashed(txn, genesis, account);
  // TODO: disconnect the node from network/ban from further participation in all Tributaries
}

pub(crate) async fn handle_application_tx<
  D: Db,
  Pro: Processors,
  FPst: Future<Output = ()>,
  PST: Clone + Fn(ValidatorSet, Encoded) -> FPst,
  FRid: Future<Output = ()>,
  RID: RIDTrait<FRid>,
>(
  tx: Transaction,
  spec: &TributarySpec,
  processors: &Pro,
  publish_serai_tx: PST,
  key: &Zeroizing<<Ristretto as Ciphersuite>::F>,
  recognized_id: RID,
  txn: &mut <D as Db>::Transaction<'_>,
) {
  let genesis = spec.genesis();

  let handle = |txn: &mut <D as Db>::Transaction<'_>,
                data_spec: &DataSpecification,
                bytes: Vec<u8>,
                signed: &Signed| {
    let Some(curr_attempt) = AttemptDb::attempt(txn, genesis, data_spec.topic) else {
      // Premature publication of a valid ID/publication of an invalid ID
      fatal_slash::<D>(
        txn,
        genesis,
        signed.signer.to_bytes(),
        "published data for ID without an attempt",
      );
      return None;
    };

    // If they've already published a TX for this attempt, slash
    if DataDb::get(txn, data_spec.as_key(genesis), signed.signer.to_bytes() as [u8; 32]).is_some() {
      fatal_slash::<D>(txn, genesis, signed.signer.to_bytes(), "published data multiple times");
      return None;
    }

    // If the attempt is lesser than the blockchain's, slash
    if data_spec.attempt < curr_attempt {
      // TODO: Slash for being late
      return None;
    }
    // If the attempt is greater, this is a premature publication, full slash
    if data_spec.attempt > curr_attempt {
      fatal_slash::<D>(
        txn,
        genesis,
        signed.signer.to_bytes(),
        "published data with an attempt which hasn't started",
      );
      return None;
    }

    // TODO: We can also full slash if shares before all commitments, or share before the
    // necessary preprocesses

    // TODO: If this is shares, we need to check they are part of the selected signing set

    // Store this data
    let recvd_key = data_spec.as_key(genesis);
    let mut received = DataReceivedDb::get(txn, &recvd_key).unwrap_or(0);
    received += 1;
    DataReceivedDb::set(txn,&recvd_key, &received);
    DataDb::set(txn, data_spec.as_key(genesis), signed.signer.to_bytes() as [u8; 32], &bytes);

    // If we have all the needed commitments/preprocesses/shares, tell the processor
    // TODO: This needs to be coded by weight, not by validator count
    let needed = if data_spec.topic == Topic::Dkg { spec.n() } else { spec.t() };
    if received == needed {
      return Some(read_known_to_exist_data::<_>(txn, spec, key, data_spec, needed));
    }
    None
  };

  match tx {
    Transaction::DkgCommitments(attempt, bytes, signed) => {
      match handle(
        txn,
        &DataSpecification { topic: Topic::Dkg, label: DKG_COMMITMENTS, attempt },
        bytes,
        &signed,
      ) {
        Some(Some(commitments)) => {
          log::info!("got all DkgCommitments for {}", hex::encode(genesis));
          processors
            .send(
              spec.set().network,
              key_gen::CoordinatorMessage::Commitments {
                id: KeyGenId { set: spec.set(), attempt },
                commitments,
              },
            )
            .await;
        }
        Some(None) => panic!("wasn't a participant in DKG commitments"),
        None => {}
      }
    }

    Transaction::DkgShares { attempt, mut shares, confirmation_nonces, signed } => {
      if shares.len() != (usize::from(spec.n()) - 1) {
        fatal_slash::<D>(txn, genesis, signed.signer.to_bytes(), "invalid amount of DKG shares");
        return;
      }

      let sender_i = spec
        .i(signed.signer)
        .expect("transaction added to tributary by signer who isn't a participant");

      // Only save our share's bytes
      let our_i = spec
        .i(Ristretto::generator() * key.deref())
        .expect("in a tributary we're not a validator for");

      let bytes = if sender_i == our_i {
        vec![]
      } else {
        // 1-indexed to 0-indexed, handling the omission of the sender's own data
        let relative_i = usize::from(u16::from(our_i) - 1) -
          (if u16::from(our_i) > u16::from(sender_i) { 1 } else { 0 });
        // Safe since we length-checked shares
        shares.swap_remove(relative_i)
      };
      drop(shares);

      let confirmation_nonces = handle(
        txn,
        &DataSpecification { topic: Topic::Dkg, label: DKG_CONFIRMATION_NONCES, attempt },
        confirmation_nonces.to_vec(),
        &signed,
      );
      match handle(
        txn,
        &DataSpecification { topic: Topic::Dkg, label: DKG_SHARES, attempt },
        bytes,
        &signed,
      ) {
        Some(Some(shares)) => {
          log::info!("got all DkgShares for {}", hex::encode(genesis));
          assert!(confirmation_nonces.is_some());
          processors
            .send(
              spec.set().network,
              key_gen::CoordinatorMessage::Shares {
                id: KeyGenId { set: spec.set(), attempt },
                shares,
              },
            )
            .await;
        }
        Some(None) => panic!("wasn't a participant in DKG shares"),
        None => assert!(confirmation_nonces.is_none()),
      }
    }

    Transaction::DkgConfirmed(attempt, shares, signed) => {
      match handle(
        txn,
        &DataSpecification { topic: Topic::Dkg, label: DKG_CONFIRMATION_SHARES, attempt },
        shares.to_vec(),
        &signed,
      ) {
        Some(Some(shares)) => {
          log::info!("got all DkgConfirmed for {}", hex::encode(genesis));

          let preprocesses = read_known_to_exist_data::<_>(
            txn,
            spec,
            key,
            &DataSpecification { topic: Topic::Dkg, label: DKG_CONFIRMATION_NONCES, attempt },
            spec.n(),
          ).expect("wasn't a participant in DKG confirmation nonces");
          let key_pair = CurrentlyCompletingKeyPairDb::get(txn, genesis)
            .expect("in DkgConfirmed handling, which happens after everyone (including us) fires DkgConfirmed, yet no confirming key pair");
          let Ok(sig) = DkgConfirmer::complete(spec, key, attempt, preprocesses, &key_pair, shares)
          else {
            // TODO: Full slash
            todo!();
          };

          publish_serai_tx(
            spec.set(),
            SeraiValidatorSets::set_keys(spec.set().network, key_pair, Signature(sig)),
          )
          .await;
        }
        Some(None) => panic!("wasn't a participant in DKG confirmination shares"),
        None => {}
      }
    }

    Transaction::Batch(_, batch) => {
      // Because this Batch has achieved synchrony, its batch ID should be authorized
      AttemptDb::set(txn, Topic::Batch(batch).as_key(genesis), &0u32.to_le_bytes());
      let nonce = NonceDecider::<D>::handle_batch(txn, genesis, batch);
      recognized_id(spec.set(), genesis, RecognizedIdType::Batch, batch, nonce).await;
    }

    Transaction::SubstrateBlock(block) => {
      let plan_ids = PlanIdsDb::get(txn, genesis, &block).map(|bytes| {
        let mut res = vec![];
        let mut bytes_ref = bytes.as_slice();
        while !bytes_ref.is_empty() {
          let mut id = [0; 32];
          bytes_ref.read_exact(&mut id).unwrap();
          res.push(id);
        }
        res
      }).expect(
        "synced a tributary block finalizing a substrate block in a provided transaction \
          despite us not providing that transaction",
      );

      let nonces = NonceDecider::<D>::handle_substrate_block(txn, genesis, &plan_ids);
      for (nonce, id) in nonces.into_iter().zip(plan_ids.into_iter()) {
        AttemptDb::set(txn, Topic::Sign(id).as_key(genesis), &0u32.to_le_bytes());
        recognized_id(spec.set(), genesis, RecognizedIdType::Plan, id, nonce).await;
      }
    }

    Transaction::BatchPreprocess(data) => {
      match handle(
        txn,
        &DataSpecification {
          topic: Topic::Batch(data.plan),
          label: BATCH_PREPROCESS,
          attempt: data.attempt,
        },
        data.data,
        &data.signed,
      ) {
        Some(Some(preprocesses)) => {
          NonceDecider::<D>::selected_for_signing_batch(txn, genesis, data.plan);
          let key = KeyPairDb::get(txn, spec.set()).unwrap().0 .0.to_vec();
          processors
            .send(
              spec.set().network,
              coordinator::CoordinatorMessage::BatchPreprocesses {
                id: SignId { key, id: data.plan, attempt: data.attempt },
                preprocesses,
              },
            )
            .await;
        }
        Some(None) => {}
        None => {}
      }
    }
    Transaction::BatchShare(data) => {
      match handle(
        txn,
        &DataSpecification {
          topic: Topic::Batch(data.plan),
          label: BATCH_SHARE,
          attempt: data.attempt,
        },
        data.data,
        &data.signed,
      ) {
        Some(Some(shares)) => {
          let key = KeyPairDb::get(txn, spec.set()).unwrap().0 .0.to_vec();
          processors
            .send(
              spec.set().network,
              coordinator::CoordinatorMessage::BatchShares {
                id: SignId { key, id: data.plan, attempt: data.attempt },
                shares: shares
                  .into_iter()
                  .map(|(validator, share)| (validator, share.try_into().unwrap()))
                  .collect(),
              },
            )
            .await;
        }
        Some(None) => {}
        None => {}
      }
    }

    Transaction::SignPreprocess(data) => {
      let key_pair = KeyPairDb::get(txn, spec.set());
      match handle(
        txn,
        &DataSpecification {
          topic: Topic::Sign(data.plan),
          label: SIGN_PREPROCESS,
          attempt: data.attempt,
        },
        data.data,
        &data.signed,
      ) {
        Some(Some(preprocesses)) => {
          NonceDecider::<D>::selected_for_signing_plan(txn, genesis, data.plan);
          processors
            .send(
              spec.set().network,
              sign::CoordinatorMessage::Preprocesses {
                id: SignId {
                  key: key_pair
                    .expect("completed SignPreprocess despite not setting the key pair")
                    .1
                    .into(),
                  id: data.plan,
                  attempt: data.attempt,
                },
                preprocesses,
              },
            )
            .await;
        }
        Some(None) => {}
        None => {}
      }
    }
    Transaction::SignShare(data) => {
      let key_pair = KeyPairDb::get(txn, spec.set());
      match handle(
        txn,
        &DataSpecification {
          topic: Topic::Sign(data.plan),
          label: SIGN_SHARE,
          attempt: data.attempt,
        },
        data.data,
        &data.signed,
      ) {
        Some(Some(shares)) => {
          processors
            .send(
              spec.set().network,
              sign::CoordinatorMessage::Shares {
                id: SignId {
                  key: key_pair
                    .expect("completed SignShares despite not setting the key pair")
                    .1
                    .into(),
                  id: data.plan,
                  attempt: data.attempt,
                },
                shares,
              },
            )
            .await;
        }
        Some(None) => {}
        None => {}
      }
    }
    Transaction::SignCompleted { plan, tx_hash, .. } => {
      log::info!(
        "on-chain SignCompleted claims {} completes {}",
        hex::encode(&tx_hash),
        hex::encode(plan)
      );
      // TODO: Confirm this is a valid plan ID
      // TODO: Confirm this signer hasn't prior published a completion
      let Some(key_pair) = KeyPairDb::get(txn, spec.set()) else { todo!() };
      processors
        .send(
          spec.set().network,
          sign::CoordinatorMessage::Completed { key: key_pair.1.to_vec(), id: plan, tx: tx_hash },
        )
        .await;
    }
  }
}
