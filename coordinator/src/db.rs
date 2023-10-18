use blake2::{
  digest::{consts::U32, Digest},
  Blake2b,
};

use scale::Encode;
use serai_client::{
  primitives::NetworkId,
  validator_sets::primitives::{Session, ValidatorSet},
  in_instructions::primitives::{Batch, SignedBatch},
};

pub use serai_db::*;

use ::tributary::ReadWrite;
use crate::tributary::{TributarySpec, Transaction, scanner::RecognizedIdType};

create_db!(
  MainDb {
    HandledMessageDb: (key: impl AsRef<[u8]>) -> Vec<u8>,
    InTributaryDb: (key: impl AsRef<[u8]>) -> Vec<u8>,
    ActiveTributaryDb: (key: impl AsRef<[u8]>) -> Vec<u8>,
    RetiredTributaryDb: (key: impl AsRef<[u8]>) -> Vec<u8>,
    SignedTransactionDb: (key: impl AsRef<[u8]>) -> Vec<u8>,
    FirstPreprocessDb: (key: impl AsRef<[u8]>) -> Vec<u8>,
    LastRecievedBatchDb: (key: impl AsRef<[u8]>) -> u32,
    ExpectedBatchDb: (key: impl AsRef<[u8]>) -> [u8; 32],
    BatchDb: (key: impl AsRef<[u8]>) -> SignedBatch,
    LastVerifiedBatchDb: (key: impl AsRef<[u8]>) -> u32,
    HandoverBatchDb: (key: impl AsRef<[u8]>) -> u32,
    LookupHandoverBatchDb: (key: impl AsRef<[u8]>) -> Session,
    QueuedBatchesDb: (key: impl AsRef<[u8]>) -> Vec<u8>
  }
);

impl ActiveTributaryDb {
  pub fn active_tributaries<G: Get>(getter: &G) -> (Vec<u8>, Vec<TributarySpec>) {
    let bytes = getter.get(Self::key(&[])).unwrap_or(vec![]);
    let mut bytes_ref: &[u8] = bytes.as_ref();

    let mut tributaries = vec![];
    while !bytes_ref.is_empty() {
      tributaries.push(TributarySpec::read(&mut bytes_ref).unwrap());
    }

    (bytes, tributaries)
  }

  pub fn retire_tributary(txn: &mut impl DbTxn, set: ValidatorSet) {
    let mut active = Self::active_tributaries(txn).1;
    for i in 0 .. active.len() {
      if active[i].set() == set {
        active.remove(i);
        break;
      }
    }

    let mut bytes = vec![];
    for active in active {
      active.write(&mut bytes).unwrap();
    }
    txn.put(Self::key(&[]), bytes);
    txn.put(RetiredTributaryDb::key(set.encode()), []);
  }
}

pub fn add_participating_in_tributary(txn: &mut impl DbTxn, spec: &TributarySpec) {
  txn.put(InTributaryDb::key(spec.set().encode()), []);

  let key = ActiveTributaryDb::key(vec![] as Vec<u8>);
  let (mut existing_bytes, existing) = ActiveTributaryDb::active_tributaries(txn);
  for tributary in &existing {
    if tributary == spec {
      return;
    }
  }

  spec.write(&mut existing_bytes).unwrap();
  txn.put(key, existing_bytes);
}

impl SignedTransactionDb {
  pub fn take_signed_transaction(txn: &mut impl DbTxn, nonce: u32) -> Option<Transaction> {
    let key = Self::key(nonce.to_le_bytes());
    let res = txn.get(&key).map(|bytes| Transaction::read(&mut bytes.as_slice()).unwrap());
    if res.is_some() {
      txn.del(&key);
    }
    res
  }
}

impl FirstPreprocessDb {
  pub fn save_first_preprocess(
    txn: &mut impl DbTxn,
    network: NetworkId,
    id_type: RecognizedIdType,
    id: [u8; 32],
    preprocess: Vec<u8>,
  ) {
    let key = Self::key((network, id_type, id).encode());
    if let Some(existing) = txn.get(&key) {
      assert_eq!(existing, preprocess, "saved a distinct first preprocess");
      return;
    }
    txn.put(key, preprocess);
  }
}

impl ExpectedBatchDb {
  pub fn save_expected_batch(txn: &mut impl DbTxn, batch: &Batch) {
    LastRecievedBatchDb::set(txn,  &batch.network.encode(), &batch.id);
    let binding = Blake2b::<U32>::digest(batch.instructions.encode());
    let data: &[u8] = binding.as_ref();
    ExpectedBatchDb::set(txn, (batch.network, batch.id).encode(), &data);
  }
}

impl HandoverBatchDb {
  pub fn set_handover_batch(txn: &mut impl DbTxn, set: ValidatorSet, batch: u32) {
    HandoverBatchDb::set(txn, set.encode(), &batch);
    LookupHandoverBatchDb::set(txn,(set.network, batch).encode(), &set.session);
  }
}
impl QueuedBatchesDb {
  pub fn queue_batch(txn: &mut impl DbTxn, set: ValidatorSet, batch: Transaction) {
    let key = Self::key(set.encode());
    let mut batches = txn.get(&key).unwrap_or(vec![]);
    batches.extend(batch.serialize());
    txn.put(&key, batches);
  }
  pub fn take_queued_batches(txn: &mut impl DbTxn, set: ValidatorSet) -> Vec<Transaction> {
    let key = Self::key(set.encode());
    let batches_vec = txn.get(&key).unwrap_or(vec![]);
    txn.del(&key);
    let mut batches: &[u8] = &batches_vec;

    let mut res = vec![];
    while !batches.is_empty() {
      res.push(Transaction::read(&mut batches).unwrap());
    }
    res
  }
}