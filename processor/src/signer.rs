use core::{marker::PhantomData, fmt};
use std::collections::{VecDeque, HashMap};

use rand_core::OsRng;

use ciphersuite::group::GroupEncoding;
use frost::{
  ThresholdKeys,
  sign::{Writable, PreprocessMachine, SignMachine, SignatureMachine},
};

use log::{info, debug, warn, error};

use scale::Encode;
use messages::sign::*;
use serai_db::create_db;
use crate::{
  Get, DbTxn, Db,
  networks::{Transaction, Eventuality, Network},
};

#[derive(Debug)]
pub enum SignerEvent<N: Network> {
  SignedTransaction { id: [u8; 32], tx: <N::Transaction as Transaction<N>>::Id },
  ProcessorMessage(ProcessorMessage),
}

create_db!(
  SignerDb {
    CompletedDb: (id: [u8; 32]) -> Vec<u8>,
    EventualityDb: (id: [u8; 32]) -> Vec<u8>,
    AttemptDb: (id: &SignId) -> [u8; 0],
    TransactionDb: (id: &[u8]) -> Vec<u8>
  }
);

impl CompletedDb {
  fn complete<N: Network>(
    txn: &mut impl DbTxn,
    id: [u8; 32],
    tx: &<N::Transaction as Transaction<N>>::Id,
  ) {
    // Transactions can be completed by multiple signatures
    // Save every solution in order to be robust
    let mut existing = Self::get(txn, id).unwrap_or(vec![]);

    // Don't add this TX if it's already present
    let tx_len = tx.as_ref().len();
    assert_eq!(existing.len() % tx_len, 0);

    let mut i = 0;
    while i < existing.len() {
      if &existing[i .. (i + tx_len)] == tx.as_ref() {
        return;
      }
      i += tx_len;
    }

    existing.extend(tx.as_ref());
    Self::set(txn, id, &existing);
  }
}

impl EventualityDb {
  fn save_eventuality<N: Network>(txn: &mut impl DbTxn, id: [u8; 32], eventuality: N::Eventuality) {
    txn.put(Self::key(id), eventuality.serialize());
  }

  fn eventuality<N: Network>(getter: &impl Get, id: [u8; 32]) -> Option<N::Eventuality> {
    Some(
      N::Eventuality::read::<&[u8]>(&mut getter.get(Self::key(id))?.as_ref()).unwrap(),
    )
  }
}

impl TransactionDb {
  fn save_transaction<N: Network>(txn: &mut impl DbTxn, tx: &N::Transaction) {
    Self::set(txn, &tx.id().as_ref(), &tx.serialize());
  }
}

pub struct Signer<N: Network, D: Db> {
  db: PhantomData<D>,

  network: N,

  keys: ThresholdKeys<N::Curve>,

  signable: HashMap<[u8; 32], N::SignableTransaction>,
  attempt: HashMap<[u8; 32], u32>,
  preprocessing: HashMap<[u8; 32], <N::TransactionMachine as PreprocessMachine>::SignMachine>,
  #[allow(clippy::type_complexity)]
  signing: HashMap<
    [u8; 32],
    <
      <N::TransactionMachine as PreprocessMachine>::SignMachine as SignMachine<N::Transaction>
    >::SignatureMachine,
  >,

  pub events: VecDeque<SignerEvent<N>>,
}

impl<N: Network, D: Db> fmt::Debug for Signer<N, D> {
  fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
    fmt
      .debug_struct("Signer")
      .field("network", &self.network)
      .field("signable", &self.signable)
      .field("attempt", &self.attempt)
      .finish_non_exhaustive()
  }
}

impl<N: Network, D: Db> Signer<N, D> {
  pub fn new(network: N, keys: ThresholdKeys<N::Curve>) -> Signer<N, D> {
    Signer {
      db: PhantomData,

      network,

      keys,

      signable: HashMap::new(),
      attempt: HashMap::new(),
      preprocessing: HashMap::new(),
      signing: HashMap::new(),

      events: VecDeque::new(),
    }
  }

  fn verify_id(&self, id: &SignId) -> Result<(), ()> {
    // Check the attempt lines up
    match self.attempt.get(&id.id) {
      // If we don't have an attempt logged, it's because the coordinator is faulty OR because we
      // rebooted OR we detected the signed transaction on chain, so there's notable network
      // latency/a malicious validator
      None => {
        warn!(
          "not attempting {} #{}. this is an error if we didn't reboot",
          hex::encode(id.id),
          id.attempt
        );
        Err(())?;
      }
      Some(attempt) => {
        if attempt != &id.attempt {
          warn!(
            "sent signing data for {} #{} yet we have attempt #{}",
            hex::encode(id.id),
            id.attempt,
            attempt
          );
          Err(())?;
        }
      }
    }

    Ok(())
  }

  fn already_completed(&self, txn: &mut D::Transaction<'_>, id: [u8; 32]) -> bool {
    if CompletedDb::get(txn, id).is_some() {
      debug!(
        "SignTransaction/Reattempt order for {}, which we've already completed signing",
        hex::encode(id)
      );

      true
    } else {
      false
    }
  }

  fn complete(&mut self, id: [u8; 32], tx_id: <N::Transaction as Transaction<N>>::Id) {
    // Assert we're actively signing for this TX
    assert!(self.signable.remove(&id).is_some(), "completed a TX we weren't signing for");
    assert!(self.attempt.remove(&id).is_some(), "attempt had an ID signable didn't have");
    // If we weren't selected to participate, we'll have a preprocess
    self.preprocessing.remove(&id);
    // If we were selected, the signature will only go through if we contributed a share
    // Despite this, we then need to get everyone's shares, and we may get a completion before
    // we get everyone's shares
    // This would be if the coordinator fails and we find the eventuality completion on-chain
    self.signing.remove(&id);

    // Emit the event for it
    self.events.push_back(SignerEvent::SignedTransaction { id, tx: tx_id });
  }

  pub fn completed(&mut self, txn: &mut D::Transaction<'_>, id: [u8; 32], tx: N::Transaction) {
    let first_completion = !self.already_completed(txn, id);

    // Save this completion to the DB
    TransactionDb::save_transaction::<N>(txn, &tx);
    CompletedDb::complete::<N>(txn, id, &tx.id());

    if first_completion {
      self.complete(id, tx.id());
    }
  }

  // Doesn't use any loops/retries since we'll eventually get this from the Scanner anyways
  async fn claimed_eventuality_completion(
    &mut self,
    txn: &mut D::Transaction<'_>,
    id: [u8; 32],
    tx_id: &<N::Transaction as Transaction<N>>::Id,
  ) -> bool {
    if let Some(eventuality) = EventualityDb::eventuality::<N>(txn, id) {
      // Transaction hasn't hit our mempool/was dropped for a different signature
      // The latter can happen given certain latency conditions/a single malicious signer
      // In the case of a single malicious signer, they can drag multiple honest validators down
      // with them, so we unfortunately can't slash on this case
      let Ok(tx) = self.network.get_transaction(tx_id).await else {
        warn!(
          "a validator claimed {} completed {} yet we didn't have that TX in our mempool {}",
          hex::encode(tx_id),
          hex::encode(id),
          "(or had another connectivity issue)",
        );
        return false;
      };

      if self.network.confirm_completion(&eventuality, &tx) {
        info!("signer eventuality for {} resolved in TX {}", hex::encode(id), hex::encode(tx_id));

        let first_completion = !self.already_completed(txn, id);

        // Save this completion to the DB
        TransactionDb::save_transaction::<N>(txn, &tx);
        CompletedDb::complete::<N>(txn, id, tx_id);

        if first_completion {
          self.complete(id, tx.id());
          return true;
        }
      } else {
        warn!(
          "a validator claimed {} completed {} when it did not",
          hex::encode(tx_id),
          hex::encode(id)
        );
      }
    } else {
      // If we don't have this in RAM, it should be because we already finished signing it
      // TODO: Will the coordinator ever send us Completed for an unknown ID?
      assert!(CompletedDb::get(txn, id).is_some());
      info!(
        "signer {} informed of the eventuality completion for plan {}, {}",
        hex::encode(self.keys.group_key().to_bytes()),
        hex::encode(id),
        "which we already marked as completed",
      );
    }
    false
  }

  async fn attempt(&mut self, txn: &mut D::Transaction<'_>, id: [u8; 32], attempt: u32) {
    if self.already_completed(txn, id) {
      return;
    }

    // Check if we're already working on this attempt
    if let Some(curr_attempt) = self.attempt.get(&id) {
      if curr_attempt >= &attempt {
        warn!(
          "told to attempt {} #{} yet we're already working on {}",
          hex::encode(id),
          attempt,
          curr_attempt
        );
        return;
      }
    }

    // Start this attempt
    // Clone the TX so we don't have an immutable borrow preventing the below mutable actions
    // (also because we do need an owned tx anyways)
    let Some(tx) = self.signable.get(&id).cloned() else {
      warn!("told to attempt a TX we aren't currently signing for");
      return;
    };

    // Delete any existing machines
    self.preprocessing.remove(&id);
    self.signing.remove(&id);

    // Update the attempt number
    self.attempt.insert(id, attempt);

    let id = SignId { key: self.keys.group_key().to_bytes().as_ref().to_vec(), id, attempt };

    info!("signing for {} #{}", hex::encode(id.id), id.attempt);

    // If we reboot mid-sign, the current design has us abort all signs and wait for latter
    // attempts/new signing protocols
    // This is distinct from the DKG which will continue DKG sessions, even on reboot
    // This is because signing is tolerant of failures of up to 1/3rd of the group
    // The DKG requires 100% participation
    // While we could apply similar tricks as the DKG (a seeded RNG) to achieve support for
    // reboots, it's not worth the complexity when messing up here leaks our secret share
    //
    // Despite this, on reboot, we'll get told of active signing items, and may be in this
    // branch again for something we've already attempted
    //
    // Only run if this hasn't already been attempted
    if AttemptDb::get(txn, &id).is_some() {
      warn!(
        "already attempted {} #{}. this is an error if we didn't reboot",
        hex::encode(id.id),
        id.attempt
      );
      return;
    }

    AttemptDb::set(txn, &id, &[] as &[u8; 0]);

    // Attempt to create the TX
    let machine = match self.network.attempt_send(self.keys.clone(), tx).await {
      Err(e) => {
        error!("failed to attempt {}, #{}: {:?}", hex::encode(id.id), id.attempt, e);
        return;
      }
      Ok(machine) => machine,
    };

    // TODO: Use a seeded RNG here so we don't produce distinct messages with the same intent
    // This is also needed so we don't preprocess, send preprocess, reboot before ack'ing the
    // message, send distinct preprocess, and then attempt a signing session premised on the former
    // with the latter
    let (machine, preprocess) = machine.preprocess(&mut OsRng);
    self.preprocessing.insert(id.id, machine);

    // Broadcast our preprocess
    self.events.push_back(SignerEvent::ProcessorMessage(ProcessorMessage::Preprocess {
      id,
      preprocess: preprocess.serialize(),
    }));
  }

  pub async fn sign_transaction(
    &mut self,
    txn: &mut D::Transaction<'_>,
    id: [u8; 32],
    tx: N::SignableTransaction,
    eventuality: N::Eventuality,
  ) {
    if self.already_completed(txn, id) {
      return;
    }

    EventualityDb::save_eventuality::<N>(txn, id, eventuality);

    self.signable.insert(id, tx);
    self.attempt(txn, id, 0).await;
  }

  pub async fn handle(&mut self, txn: &mut D::Transaction<'_>, msg: CoordinatorMessage) {
    match msg {
      CoordinatorMessage::Preprocesses { id, mut preprocesses } => {
        if self.verify_id(&id).is_err() {
          return;
        }

        let machine = match self.preprocessing.remove(&id.id) {
          // Either rebooted or RPC error, or some invariant
          None => {
            warn!(
              "not preprocessing for {}. this is an error if we didn't reboot",
              hex::encode(id.id)
            );
            return;
          }
          Some(machine) => machine,
        };

        let preprocesses = match preprocesses
          .drain()
          .map(|(l, preprocess)| {
            let mut preprocess_ref = preprocess.as_ref();
            let res = machine
              .read_preprocess::<&[u8]>(&mut preprocess_ref)
              .map(|preprocess| (l, preprocess));
            if !preprocess_ref.is_empty() {
              todo!("malicious signer: extra bytes");
            }
            res
          })
          .collect::<Result<_, _>>()
        {
          Ok(preprocesses) => preprocesses,
          Err(e) => todo!("malicious signer: {:?}", e),
        };

        // Use an empty message, as expected of TransactionMachines
        let (machine, share) = match machine.sign(preprocesses, &[]) {
          Ok(res) => res,
          Err(e) => todo!("malicious signer: {:?}", e),
        };
        self.signing.insert(id.id, machine);

        // Broadcast our share
        self.events.push_back(SignerEvent::ProcessorMessage(ProcessorMessage::Share {
          id,
          share: share.serialize(),
        }));
      }

      CoordinatorMessage::Shares { id, mut shares } => {
        if self.verify_id(&id).is_err() {
          return;
        }

        let machine = match self.signing.remove(&id.id) {
          // Rebooted, RPC error, or some invariant
          None => {
            // If preprocessing has this ID, it means we were never sent the preprocess by the
            // coordinator
            if self.preprocessing.contains_key(&id.id) {
              panic!("never preprocessed yet signing?");
            }

            warn!(
              "not preprocessing for {}. this is an error if we didn't reboot",
              hex::encode(id.id)
            );
            return;
          }
          Some(machine) => machine,
        };

        let shares = match shares
          .drain()
          .map(|(l, share)| {
            let mut share_ref = share.as_ref();
            let res = machine.read_share::<&[u8]>(&mut share_ref).map(|share| (l, share));
            if !share_ref.is_empty() {
              todo!("malicious signer: extra bytes");
            }
            res
          })
          .collect::<Result<_, _>>()
        {
          Ok(shares) => shares,
          Err(e) => todo!("malicious signer: {:?}", e),
        };

        let tx = match machine.complete(shares) {
          Ok(res) => res,
          Err(e) => todo!("malicious signer: {:?}", e),
        };

        // Save the transaction in case it's needed for recovery
        TransactionDb::save_transaction::<N>(txn, &tx);
        let tx_id = tx.id();
        CompletedDb::complete::<N>(txn, id.id, &tx_id);

        // Publish it
        if let Err(e) = self.network.publish_transaction(&tx).await {
          error!("couldn't publish {:?}: {:?}", tx, e);
        } else {
          info!("published {} for plan {}", hex::encode(&tx_id), hex::encode(id.id));
        }

        // Stop trying to sign for this TX
        self.complete(id.id, tx_id);
      }

      CoordinatorMessage::Reattempt { id } => {
        self.attempt(txn, id.id, id.attempt).await;
      }

      CoordinatorMessage::Completed { key: _, id, tx: mut tx_vec } => {
        let mut tx = <N::Transaction as Transaction<N>>::Id::default();
        if tx.as_ref().len() != tx_vec.len() {
          let true_len = tx_vec.len();
          tx_vec.truncate(2 * tx.as_ref().len());
          warn!(
            "a validator claimed {}... (actual length {}) completed {} yet {}",
            hex::encode(&tx_vec),
            true_len,
            hex::encode(id),
            "that's not a valid TX ID",
          );
          return;
        }
        tx.as_mut().copy_from_slice(&tx_vec);

        self.claimed_eventuality_completion(txn, id, &tx).await;
      }
    }
  }
}
