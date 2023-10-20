use ciphersuite::Ciphersuite;

pub use serai_db::*;

use scale::{Encode, Decode};
use serai_client::in_instructions::primitives::InInstructionWithBalance;

use crate::{
  Get, Plan,
  networks::{Transaction, Network},
};

create_db!(
  MultisigsDb {
    NextBatchDb: () -> u32,
    PlanDb: (id: &[u8]) -> Vec<u8>,
    OperatingCostsDb: () -> u64,
    ResolvedDb: (tx: &[u8]) -> [u8; 32],
    SigningDb: (key: &[u8]) -> Vec<u8>,
    ForwardedOutputDb: (amount: u64) -> Vec<u8>,
    DelayedOutputDb: () -> Vec<u8>
  }
);

impl PlanDb {
  pub fn save_active_plan<N: Network>(
    txn: &mut impl DbTxn,
    key: &[u8],
    block_number: u64,
    plan: &Plan<N>,
    operating_costs_at_time: u64,
  ) {
    let id = plan.id();

    {
      let mut signing = SigningDb::get(txn, key).unwrap_or(vec![]);

      // If we've already noted we're signing this, return
      assert_eq!(signing.len() % 32, 0);
      for i in 0 .. (signing.len() / 32) {
        if signing[(i * 32) .. ((i + 1) * 32)] == id {
          return;
        }
      }

      signing.extend(&id);
      SigningDb::set(txn, key, &id);
    }

    {
      let mut buf = block_number.to_le_bytes().to_vec();
      plan.write(&mut buf).unwrap();
      Self::set(txn, &id, &buf);
    }
  }

  pub fn active_plans<N: Network>(getter: &impl Get, key: &[u8]) -> Vec<(u64, Plan<N>, u64)> {
    let signing = SigningDb::get(getter, key).unwrap_or(vec![]);
    let mut res = vec![];

    assert_eq!(signing.len() % 32, 0);
    for i in 0 .. (signing.len() / 32) {
      let id = &signing[(i * 32) .. ((i + 1) * 32)];
      let buf = Self::get(getter, id).unwrap();

      let block_number = u64::from_le_bytes(buf[.. 8].try_into().unwrap());
      let plan = Plan::<N>::read::<&[u8]>(&mut &buf[8 ..]).unwrap();
      assert_eq!(id, &plan.id());
      let operating_costs = u64::from_le_bytes(buf[(buf.len() - 8) ..].try_into().unwrap());
      res.push((block_number, plan, operating_costs));
    }
    res
  }

  pub fn plan_by_key_with_self_change<N: Network>(
    getter: &impl Get,
    key: <N::Curve as Ciphersuite>::G,
    id: [u8; 32],
  ) -> bool {
    let plan =
      Plan::<N>::read::<&[u8]>(&mut &Self::get(getter, &id).unwrap()[8 ..]).unwrap();
    assert_eq!(plan.id(), id);
    (key == plan.key) && (Some(N::change_address(plan.key)) == plan.change)
  }
}

impl OperatingCostsDb {
  pub fn take_operating_costs(txn: &mut impl DbTxn) -> u64 {
    let existing = Self::get(txn).unwrap();
    txn.del(Self::key());
    existing
  }
  pub fn set_operating_costs(txn: &mut impl DbTxn, amount: u64) {
    if amount != 0 {
      Self::set(txn, &amount);
    }
  }
}
impl ResolvedDb {
  pub fn resolve_plan<N: Network>(
    txn: &mut impl DbTxn,
    key: &[u8],
    plan: [u8; 32],
    resolution: <N::Transaction as Transaction<N>>::Id,
  ) {
    let mut signing = SigningDb::get(txn, key).unwrap_or(vec![]);
    assert_eq!(signing.len() % 32, 0);

    let mut found = false;
    for i in 0 .. (signing.len() / 32) {
      let start = i * 32;
      let end = i + 32;
      if signing[start .. end] == plan {
        found = true;
        signing = [&signing[.. start], &signing[end ..]].concat().to_vec();
        break;
      }
    }

    if !found {
      log::warn!("told to finish signing {} yet wasn't actively signing it", hex::encode(plan));
    }
    SigningDb::set(txn, key, &signing);
    Self::set(txn, resolution.as_ref(), &plan);
  }
}

impl ForwardedOutputDb {
  pub fn save_forwarded_output(
    txn: &mut impl DbTxn,
    instruction: InInstructionWithBalance,
  ) {
    let mut existing = Self::get(txn, instruction.balance.amount.0).unwrap();
    existing.extend(instruction.encode());
    Self::set(txn, instruction.balance.amount.0, &existing);
  }

  pub fn take_forwarded_output(
    txn: &mut impl DbTxn,
    amount: u64,
  ) -> Option<InInstructionWithBalance> {
    let outputs = Self::get(txn, amount).unwrap();
    let mut outputs_ref = outputs.as_slice();
    let res = InInstructionWithBalance::decode(&mut outputs_ref).unwrap();
    assert!(outputs_ref.len() < outputs.len());
    if outputs_ref.is_empty() {
      txn.del(&Self::key(amount));
    } else {
      Self::set(txn, amount, &outputs);
    }
    Some(res)
  }
}

impl DelayedOutputDb {
  pub fn save_delayed_output(txn: &mut impl DbTxn, instruction: InInstructionWithBalance) {
    let mut existing = Self::get(txn).unwrap_or(vec![]);
    existing.extend(instruction.encode());
    Self::set(txn, &existing);
  }

  pub fn take_delayed_outputs(txn: &mut impl DbTxn) -> Vec<InInstructionWithBalance> {
    let Some(outputs) = Self::get(txn) else { return vec![] };
    txn.del(Self::key());

    let mut outputs_ref = outputs.as_slice();
    let mut res = vec![];
    while !outputs_ref.is_empty() {
      res.push(InInstructionWithBalance::decode(&mut outputs_ref).unwrap());
    }
    res
  }
}
