use serai_client::validator_sets::primitives::KeyPair;

use serai_db::create_db;

pub use serai_db::*;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Topic {
  Dkg,
  Batch([u8; 32]),
  Sign([u8; 32]),
}

impl Topic {
  pub fn as_key(&self, genesis: [u8; 32]) -> Vec<u8> {
    let mut res = genesis.to_vec();
    let (label, id) = match self {
      Topic::Dkg => (b"dkg".as_slice(), [].as_slice()),
      Topic::Batch(id) => (b"batch".as_slice(), id.as_slice()),
      Topic::Sign(id) => (b"sign".as_slice(), id.as_slice()),
    };
    res.push(u8::try_from(label.len()).unwrap());
    res.extend(label);
    res.push(u8::try_from(id.len()).unwrap());
    res.extend(id);
    res
  }
}

// A struct to refer to a piece of data all validators will presumably provide a value for.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct DataSpecification {
  pub topic: Topic,
  pub label: &'static str,
  pub attempt: u32,
}

impl DataSpecification {
  pub fn as_key(&self, genesis: [u8; 32]) -> Vec<u8> {
    let mut res = self.topic.as_key(genesis);
    let label_bytes = self.label.bytes();
    res.push(u8::try_from(label_bytes.len()).unwrap());
    res.extend(label_bytes);
    res.extend(self.attempt.to_le_bytes());
    res
  }
}

create_db!(
  TributaryDb {
    LastBlockDb: [u8; 32],
    FatalSlashesDb: Vec<u8>,
    FatallySlashedDb: Vec<u8>,
    PlanIdsDb: Vec<u8>,
    CurrentlyCompletingKeyPairDb: KeyPair,
    KeyPairDb: KeyPair,
    AttemptDb: Vec<u8>,
    DataReceivedDb: Vec<u8>,
    DataDb: Vec<u8>,
    EventDb: Vec<u8>
  }
);

impl FatallySlashedDb {
  pub fn set_fatally_slashed(txn: &mut impl DbTxn, genesis: [u8; 32], account: [u8; 32]) {
    Self::set(txn, account, &[] as &[u8; 0]);
    let key = FatalSlashesDb::key(genesis);
    let mut existing = txn.get(&key).unwrap_or_default();
    if existing.chunks(32).any(|existing| existing == account) {
      return;
    }
    existing.extend(account);
    txn.put(key, existing);
  }
}

impl AttemptDb {
  pub fn attempt(getter: &impl Get, genesis: [u8; 32], topic: Topic) -> Option<u32> {
    let attempt_bytes = Self::get(getter, topic.as_key(genesis));

    // DKGs start when the chain starts
    if attempt_bytes.is_none() && (topic == Topic::Dkg) {
      return Some(0);
    }
    Some(u32::from_le_bytes(attempt_bytes?.try_into().unwrap()))
  }
}