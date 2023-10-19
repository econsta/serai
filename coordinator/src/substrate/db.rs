use scale::Encode;

pub use serai_db::*;

use serai_client::{
  primitives::NetworkId,
  validator_sets::primitives::{Session, KeyPair},
};
create_db!(
  SubstrateDb {
    BlockDb: () -> u64,
    SubstrateEventDb: (id: [u8; 32], index: u32) -> Vec<u8>,
    SessionDb: (id: &Vec<u8>) -> Session,
    BatchInstructionDb: (network: NetworkId, id: u32) -> [u8; 32]
  }
);

impl SubstrateEventDb {
  pub fn handle_event(txn: &mut impl DbTxn, id: [u8; 32], index: u32) {
    assert!(Self::get(txn, id, index).is_none());
    Self::set(txn, id, index, &vec![] as &Vec<u8>);
  }
}

impl SessionDb {
  pub fn save_session_for_keys(txn: &mut impl DbTxn, key_pair: &KeyPair, session: Session) {
    let existing = Self::get(txn, &key_pair.0.encode());
    // This may trigger if 100% of a DKG are malicious, and they create a key equivalent to a prior
    // key. Since it requires 100% maliciousness, not just 67% maliciousness, this will only assert
    // in a modified-to-be-malicious stack, making it safe
    assert!(existing.is_none() || (existing.as_ref() == Some(&session)));
    Self::set(txn, &key_pair.0.encode(), &session.clone());
    Self::set(txn, &key_pair.1.encode(), &session);
  }
}