use core::marker::PhantomData;

use serai_db::{Get, DbTxn, Db, create_db};

use crate::tributary::Transaction;

use scale::Encode;

/// Decides the nonce which should be used for a transaction on a Tributary.
///
/// Deterministically builds a list of nonces to use based on the on-chain events and expected
/// transactions in response. Enables rebooting/rebuilding validators with full safety.
pub struct NonceDecider<D: Db>(PhantomData<D>);

const BATCH_CODE: u8 = 0;
const BATCH_SIGNING_CODE: u8 = 1;
const PLAN_CODE: u8 = 2;
const PLAN_SIGNING_CODE: u8 = 3;

create_db!(
  CoordinatorTributaryDb {
    NextNonceDb: (genesis: &[u8]) -> u32,
    ItemNonceDb: (genesis: &[u8], code: &[u8], id: &[u8]) -> u32
  }
);



impl<D: Db> NonceDecider<D> {
  fn allocate_nonce(txn: &mut impl DbTxn, genesis: [u8; 32]) -> u32 {
    let next = NextNonceDb::get(txn, &genesis).unwrap_or(3);
    NextNonceDb::set(txn, &genesis, &(next + 1));
    next
  }
  
  fn set_nonce(
    txn: &mut D::Transaction<'_>,
    genesis: [u8; 32],
    code: u8,
    id: [u8; 32],
    nonce: u32,
  ) {
    ItemNonceDb::set(txn, &genesis, [code].as_ref(), &id, &nonce);
  }

  fn db_nonce(getter: &impl Get, genesis: [u8; 32], code: u8, id: [u8; 32]) -> Option<u32> {
    ItemNonceDb::get(getter, &genesis, [code].as_ref(), &id)
  }

  pub fn handle_batch(txn: &mut D::Transaction<'_>, genesis: [u8; 32], batch: [u8; 32]) -> u32 {
    let nonce_for = Self::allocate_nonce(txn, genesis);
    Self::set_nonce(txn, genesis, BATCH_CODE, batch, nonce_for);
    nonce_for
  }
  pub fn selected_for_signing_batch(
    txn: &mut D::Transaction<'_>,
    genesis: [u8; 32],
    batch: [u8; 32],
  ) {
    let nonce_for = Self::allocate_nonce(txn, genesis);
    Self::set_nonce(txn, genesis, BATCH_SIGNING_CODE, batch, nonce_for);
  }

  pub fn handle_substrate_block(
    txn: &mut D::Transaction<'_>,
    genesis: [u8; 32],
    plans: &[[u8; 32]],
  ) -> Vec<u32> {
    let mut res = Vec::with_capacity(plans.len());
    for plan in plans {
      let nonce_for = Self::allocate_nonce(txn, genesis);
      Self::set_nonce(txn, genesis, PLAN_CODE, *plan, nonce_for);
      res.push(nonce_for);
    }
    res
  }
  pub fn selected_for_signing_plan(
    txn: &mut D::Transaction<'_>,
    genesis: [u8; 32],
    plan: [u8; 32],
  ) {
    let nonce_for = Self::allocate_nonce(txn, genesis);
    Self::set_nonce(txn, genesis, PLAN_SIGNING_CODE, plan, nonce_for);
  }

  pub fn nonce<G: Get>(getter: &G, genesis: [u8; 32], tx: &Transaction) -> Option<Option<u32>> {
    match tx {
      Transaction::DkgCommitments(attempt, _, _) => {
        assert_eq!(*attempt, 0);
        Some(Some(0))
      }
      Transaction::DkgShares { attempt, .. } => {
        assert_eq!(*attempt, 0);
        Some(Some(1))
      }
      Transaction::DkgConfirmed(attempt, _, _) => {
        assert_eq!(*attempt, 0);
        Some(Some(2))
      }

      Transaction::Batch(_, _) => None,
      Transaction::SubstrateBlock(_) => None,

      Transaction::BatchPreprocess(data) => {
        assert_eq!(data.attempt, 0);
        Some(Self::db_nonce(getter, genesis, BATCH_CODE, data.plan))
      }
      Transaction::BatchShare(data) => {
        assert_eq!(data.attempt, 0);
        Some(Self::db_nonce(getter, genesis, BATCH_SIGNING_CODE, data.plan))
      }

      Transaction::SignPreprocess(data) => {
        assert_eq!(data.attempt, 0);
        Some(Self::db_nonce(getter, genesis, PLAN_CODE, data.plan))
      }
      Transaction::SignShare(data) => {
        assert_eq!(data.attempt, 0);
        Some(Self::db_nonce(getter, genesis, PLAN_SIGNING_CODE, data.plan))
      }

      Transaction::SignCompleted { .. } => None,
    }
  }
}
