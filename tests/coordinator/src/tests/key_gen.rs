use std::{
  sync::Mutex,
  time::{Duration, SystemTime},
  collections::HashMap,
};

use zeroize::Zeroizing;
use rand_core::OsRng;

use ciphersuite::{
  group::{ff::Field, GroupEncoding},
  Ciphersuite, Ristretto, Secp256k1,
};
use dkg::{Participant, ThresholdParams};

use serai_client::{
  primitives::NetworkId,
  Public,
  validator_sets::primitives::{Session, ValidatorSet},
};
use messages::{key_gen::KeyGenId, CoordinatorMessage};

use crate::{*, tests::*};

pub async fn key_gen<C: Ciphersuite>(
  processors: &mut [Processor],
) -> (Zeroizing<<Ristretto as Ciphersuite>::F>, Zeroizing<C::F>) {
  let participant_from_i = |i: usize| Participant::new(u16::try_from(i + 1).unwrap()).unwrap();

  let set = ValidatorSet { session: Session(0), network: NetworkId::Bitcoin };
  let id = KeyGenId { set, attempt: 0 };

  for (i, processor) in processors.iter_mut().enumerate() {
    assert_eq!(
      processor.recv_message().await,
      CoordinatorMessage::KeyGen(messages::key_gen::CoordinatorMessage::GenerateKey {
        id,
        params: ThresholdParams::new(
          u16::try_from(((COORDINATORS * 2) / 3) + 1).unwrap(),
          u16::try_from(COORDINATORS).unwrap(),
          participant_from_i(i),
        )
        .unwrap()
      })
    );

    processor
      .send_message(messages::key_gen::ProcessorMessage::Commitments {
        id,
        commitments: vec![u8::try_from(i).unwrap()],
      })
      .await;
  }

  wait_for_tributary().await;
  for (i, processor) in processors.iter_mut().enumerate() {
    let mut commitments = (0 .. u8::try_from(COORDINATORS).unwrap())
      .map(|l| (participant_from_i(l.into()), vec![l]))
      .collect::<HashMap<_, _>>();
    commitments.remove(&participant_from_i(i));
    assert_eq!(
      processor.recv_message().await,
      CoordinatorMessage::KeyGen(messages::key_gen::CoordinatorMessage::Commitments {
        id,
        commitments,
      })
    );

    // from (0 .. n), to (1 ..= n)
    let mut shares = (0 .. u8::try_from(COORDINATORS).unwrap())
      .map(|l| (participant_from_i(l.into()), vec![u8::try_from(i).unwrap(), l + 1]))
      .collect::<HashMap<_, _>>();

    let i = participant_from_i(i);
    shares.remove(&i);
    processor.send_message(messages::key_gen::ProcessorMessage::Shares { id, shares }).await;
  }

  let substrate_priv_key = Zeroizing::new(<Ristretto as Ciphersuite>::F::random(&mut OsRng));
  let substrate_key = (<Ristretto as Ciphersuite>::generator() * *substrate_priv_key).to_bytes();

  let network_priv_key = Zeroizing::new(C::F::random(&mut OsRng));
  let network_key = (C::generator() * *network_priv_key).to_bytes().as_ref().to_vec();

  let serai = processors[0].serai().await;
  let mut last_serai_block = serai.get_latest_block().await.unwrap().number();

  wait_for_tributary().await;
  for (i, processor) in processors.iter_mut().enumerate() {
    let i = participant_from_i(i);
    assert_eq!(
      processor.recv_message().await,
      CoordinatorMessage::KeyGen(messages::key_gen::CoordinatorMessage::Shares {
        id,
        shares: {
          let mut shares = (0 .. u8::try_from(COORDINATORS).unwrap())
            .map(|l| (participant_from_i(l.into()), vec![l, u8::try_from(u16::from(i)).unwrap()]))
            .collect::<HashMap<_, _>>();
          shares.remove(&i);
          shares
        },
      })
    );
    processor
      .send_message(messages::key_gen::ProcessorMessage::GeneratedKeyPair {
        id,
        substrate_key,
        network_key: network_key.clone(),
      })
      .await;
  }

  // Sleeps for longer since we need to wait for a Substrate block as well
  'outer: for _ in 0 .. 20 {
    tokio::time::sleep(Duration::from_secs(6)).await;
    if std::env::var("GITHUB_CI") == Ok("true".to_string()) {
      tokio::time::sleep(Duration::from_secs(6)).await;
    }

    while last_serai_block <= serai.get_latest_block().await.unwrap().number() {
      if !serai
        .get_key_gen_events(
          serai.get_block_by_number(last_serai_block).await.unwrap().unwrap().hash(),
        )
        .await
        .unwrap()
        .is_empty()
      {
        break 'outer;
      }
      last_serai_block += 1;
    }
  }
  let mut message = None;
  for processor in processors.iter_mut() {
    let msg = processor.recv_message().await;
    if message.is_none() {
      match msg {
        CoordinatorMessage::Substrate(
          messages::substrate::CoordinatorMessage::ConfirmKeyPair {
            context,
            set: this_set,
            ref key_pair,
          },
        ) => {
          assert!(
            SystemTime::now()
              .duration_since(SystemTime::UNIX_EPOCH)
              .unwrap()
              .as_secs()
              .abs_diff(context.serai_time) <
              70
          );
          assert_eq!(context.network_latest_finalized_block.0, [0; 32]);
          assert_eq!(set, this_set);
          assert_eq!(key_pair.0 .0, substrate_key);
          assert_eq!(&key_pair.1, &network_key);
        }
        _ => panic!("coordinator didn't respond with ConfirmKeyPair"),
      }
      message = Some(msg);
    } else {
      assert_eq!(message, Some(msg));
    }
  }
  assert_eq!(
    serai.get_keys(set).await.unwrap().unwrap(),
    (Public(substrate_key), network_key.try_into().unwrap())
  );

  (substrate_priv_key, network_priv_key)
}

#[tokio::test]
async fn key_gen_test() {
  let _one_at_a_time = ONE_AT_A_TIME.get_or_init(|| Mutex::new(())).lock();
  let (processors, test) = new_test();

  test
    .run_async(|ops| async move {
      // Wait for the Serai node to boot, and for the Tendermint chain to get past the first block
      // TODO: Replace this with a Coordinator RPC
      tokio::time::sleep(Duration::from_secs(150)).await;

      // Sleep even longer if in the CI due to it being slower than commodity hardware
      if std::env::var("GITHUB_CI") == Ok("true".to_string()) {
        tokio::time::sleep(Duration::from_secs(120)).await;
      }

      // Connect to the Message Queues as the processor
      let mut new_processors: Vec<Processor> = vec![];
      for (handles, key) in processors {
        new_processors.push(Processor::new(NetworkId::Bitcoin, &ops, handles, key).await);
      }
      let mut processors = new_processors;

      key_gen::<Secp256k1>(&mut processors).await;
    })
    .await;
}
