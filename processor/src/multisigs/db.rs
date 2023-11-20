use core::marker::PhantomData;

use bitcoin_serai::bitcoin::block;
use ciphersuite::Ciphersuite;

use futures::executor::block_on;
pub use serai_db::*;

use scale::{Encode, Decode};
use serai_client::{primitives::Balance, in_instructions::primitives::InInstructionWithBalance};

use crate::{
  Get, Plan,
  networks::{Transaction, Network},
};

create_db!(
  MultisigsDb {
    NextBatchDb: () -> u32,
    PlanDb: (id: &[u8]) -> Vec<u8>,
    PlansFromScanningDb: (block_number: u64) -> Vec<u8>,
    OperatingCostsDb: () -> u64,
    ResolvedDb: (tx: &[u8]) -> [u8; 32],
    SigningDb: (key: &[u8]) -> Vec<u8>,
    ForwardedOutputDb: (balance: Balance) -> Vec<u8>,
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
      let mut signing = SigningDb::get(txn, key).unwrap_or_default();

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
      buf.extend(&operating_costs_at_time.to_le_bytes());
      plan.write(&mut buf).unwrap();
      Self::set(txn, &id, &buf);
    }
  }

  pub fn active_plans<N: Network>(getter: &impl Get, key: &[u8]) -> Vec<(u64, Plan<N>, u64)> {
    let signing = SigningDb::get(getter, key).unwrap_or_default();
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

impl PlansFromScanningDb {
  pub fn set_plans_from_scanning<N: Network>(
    txn: &mut impl DbTxn,
    block_number: u64,
    plans: Vec<Plan<N>>,
  ) {
    let mut buf = vec![];
    for plan in plans {
      plan.write(&mut buf).unwrap();
    }
    Self::set(txn, block_number, &buf);
  }

  pub fn take_plans_from_scanning<N: Network>(
    txn:&mut impl DbTxn,
    block_number: u64,
  ) -> Option<Vec<Plan<N>>> {
    let res = PlansFromScanningDb::get(txn, block_number).map(|plans| {
      let mut plans_ref = plans.as_slice();
      let mut res = vec![];
      while !plans_ref.is_empty() {
        res.push(Plan::<N>::read(&mut plans_ref).unwrap());
      }
      res
    });
    if res.is_some() {
      txn.del(Self::key(block_number));
    }
    res
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
    let mut signing = SigningDb::get(txn, key).unwrap_or_default();
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
    let mut existing = Self::get(txn, instruction.balance).unwrap();
    existing.extend(instruction.encode());
    Self::set(txn, instruction.balance, &existing);
  }

  pub fn take_forwarded_output(
    txn: &mut impl DbTxn,
    balance: Balance,
  ) -> Option<InInstructionWithBalance> {
    let outputs = Self::get(txn, balance)?;
    let mut outputs_ref = outputs.as_slice();
    let res = InInstructionWithBalance::decode(&mut outputs_ref).unwrap();
    assert!(outputs_ref.len() < outputs.len());
    if outputs_ref.is_empty() {
      txn.del(&Self::key(balance));
    } else {
      Self::set(txn, balance, &outputs);
    }
    Some(res)
  }
}

impl DelayedOutputDb {
  pub fn save_delayed_output(txn: &mut impl DbTxn, instruction: InInstructionWithBalance) {
    let mut existing = Self::get(txn).unwrap_or_default();
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

// #[derive(Debug)]
// pub struct MultisigsDb<N: Network, D: Db>(PhantomData<N>, PhantomData<D>);
// impl<N: Network, D: Db> MultisigsDb<N, D> {
//   fn multisigs_key(dst: &'static [u8], key: impl AsRef<[u8]>) -> Vec<u8> {
//     D::key(b"MULTISIGS", dst, key)
//   }

//   fn next_batch_key() -> Vec<u8> {
//     Self::multisigs_key(b"next_batch", [])
//   }
//   // Set the next batch ID to use
//   pub fn set_next_batch_id(txn: &mut D::Transaction<'_>, batch: u32) {
//     txn.put(Self::next_batch_key(), batch.to_le_bytes());
//   }
//   // Get the next batch ID
//   pub fn next_batch_id<G: Get>(getter: &G) -> u32 {
//     getter.get(Self::next_batch_key()).map_or(0, |v| u32::from_le_bytes(v.try_into().unwrap()))
//   }

//   fn plan_key(id: &[u8]) -> Vec<u8> {
//     Self::multisigs_key(b"plan", id)
//   }
//   fn resolved_key(tx: &[u8]) -> Vec<u8> {
//     Self::multisigs_key(b"resolved", tx)
//   }
//   fn signing_key(key: &[u8]) -> Vec<u8> {
//     Self::multisigs_key(b"signing", key)
//   }
//   pub fn save_active_plan(
//     txn: &mut D::Transaction<'_>,
//     key: &[u8],
//     block_number: u64,
//     plan: &Plan<N>,
//     operating_costs_at_time: u64,
//   ) {
//     let id = plan.id();

//     {
//       let mut signing = txn.get(Self::signing_key(key)).unwrap_or(vec![]);

//       // If we've already noted we're signing this, return
//       assert_eq!(signing.len() % 32, 0);
//       for i in 0 .. (signing.len() / 32) {
//         if signing[(i * 32) .. ((i + 1) * 32)] == id {
//           return;
//         }
//       }

//       signing.extend(&id);
//       txn.put(Self::signing_key(key), id);
//     }

//     {
//       let mut buf = block_number.to_le_bytes().to_vec();
//       plan.write(&mut buf).unwrap();
//       buf.extend(&operating_costs_at_time.to_le_bytes());
//       txn.put(Self::plan_key(&id), &buf);
//     }
//   }

//   pub fn active_plans<G: Get>(getter: &G, key: &[u8]) -> Vec<(u64, Plan<N>, u64)> {
//     let signing = getter.get(Self::signing_key(key)).unwrap_or(vec![]);
//     let mut res = vec![];

//     assert_eq!(signing.len() % 32, 0);
//     for i in 0 .. (signing.len() / 32) {
//       let id = &signing[(i * 32) .. ((i + 1) * 32)];
//       let buf = getter.get(Self::plan_key(id)).unwrap();

//       let block_number = u64::from_le_bytes(buf[.. 8].try_into().unwrap());
//       let plan = Plan::<N>::read::<&[u8]>(&mut &buf[8 ..]).unwrap();
//       assert_eq!(id, &plan.id());
//       let operating_costs = u64::from_le_bytes(buf[(buf.len() - 8) ..].try_into().unwrap());
//       res.push((block_number, plan, operating_costs));
//     }

//     res
//   }

//   fn operating_costs_key() -> Vec<u8> {
//     Self::multisigs_key(b"operating_costs", [])
//   }
//   pub fn take_operating_costs(txn: &mut D::Transaction<'_>) -> u64 {
//     let existing = txn
//       .get(Self::operating_costs_key())
//       .map(|bytes| u64::from_le_bytes(bytes.try_into().unwrap()))
//       .unwrap_or(0);
//     txn.del(Self::operating_costs_key());
//     existing
//   }
//   pub fn set_operating_costs(txn: &mut D::Transaction<'_>, amount: u64) {
//     if amount != 0 {
//       txn.put(Self::operating_costs_key(), amount.to_le_bytes());
//     }
//   }

//   pub fn resolved_plan<G: Get>(
//     getter: &G,
//     tx: <N::Transaction as Transaction<N>>::Id,
//   ) -> Option<[u8; 32]> {
//     getter.get(Self::resolved_key(tx.as_ref())).map(|id| id.try_into().unwrap())
//   }
//   pub fn plan_by_key_with_self_change<G: Get>(
//     getter: &G,
//     key: <N::Curve as Ciphersuite>::G,
//     id: [u8; 32],
//   ) -> bool {
//     let plan =
//       Plan::<N>::read::<&[u8]>(&mut &getter.get(Self::plan_key(&id)).unwrap()[8 ..]).unwrap();
//     assert_eq!(plan.id(), id);
//     (key == plan.key) && (Some(N::change_address(plan.key)) == plan.change)
//   }
//   pub fn resolve_plan(
//     txn: &mut D::Transaction<'_>,
//     key: &[u8],
//     plan: [u8; 32],
//     resolution: <N::Transaction as Transaction<N>>::Id,
//   ) {
//     let mut signing = txn.get(Self::signing_key(key)).unwrap_or(vec![]);
//     assert_eq!(signing.len() % 32, 0);

//     let mut found = false;
//     for i in 0 .. (signing.len() / 32) {
//       let start = i * 32;
//       let end = i + 32;
//       if signing[start .. end] == plan {
//         found = true;
//         signing = [&signing[.. start], &signing[end ..]].concat().to_vec();
//         break;
//       }
//     }

//     if !found {
//       log::warn!("told to finish signing {} yet wasn't actively signing it", hex::encode(plan));
//     }

//     txn.put(Self::signing_key(key), signing);

//     txn.put(Self::resolved_key(resolution.as_ref()), plan);
//   }

//   fn plans_from_scanning_key(block_number: usize) -> Vec<u8> {
//     Self::multisigs_key(b"plans_from_scanning", u32::try_from(block_number).unwrap().to_le_bytes())
//   }
//   pub fn set_plans_from_scanning(
//     txn: &mut D::Transaction<'_>,
//     block_number: usize,
//     plans: Vec<Plan<N>>,
//   ) {
//     let mut buf = vec![];
//     for plan in plans {
//       plan.write(&mut buf).unwrap();
//     }
//     txn.put(Self::plans_from_scanning_key(block_number), buf);
//   }
//   pub fn take_plans_from_scanning(
//     txn: &mut D::Transaction<'_>,
//     block_number: usize,
//   ) -> Option<Vec<Plan<N>>> {
//     let key = Self::plans_from_scanning_key(block_number);
//     let res = txn.get(&key).map(|plans| {
//       let mut plans_ref = plans.as_slice();
//       let mut res = vec![];
//       while !plans_ref.is_empty() {
//         res.push(Plan::<N>::read(&mut plans_ref).unwrap());
//       }
//       res
//     });
//     if res.is_some() {
//       txn.del(key);
//     }
//     res
//   }

//   fn forwarded_output_key(balance: Balance) -> Vec<u8> {
//     Self::multisigs_key(b"forwarded_output", balance.encode())
//   }
//   pub fn save_forwarded_output(
//     txn: &mut D::Transaction<'_>,
//     instruction: InInstructionWithBalance,
//   ) {
//     let key = Self::forwarded_output_key(instruction.balance);
//     let mut existing = txn.get(&key).unwrap_or(vec![]);
//     existing.extend(instruction.encode());
//     txn.put(key, existing);
//   }
//   pub fn take_forwarded_output(
//     txn: &mut D::Transaction<'_>,
//     balance: Balance,
//   ) -> Option<InInstructionWithBalance> {
//     let key = Self::forwarded_output_key(balance);

//     let outputs = txn.get(&key)?;
//     let mut outputs_ref = outputs.as_slice();

//     let res = InInstructionWithBalance::decode(&mut outputs_ref).unwrap();
//     assert!(outputs_ref.len() < outputs.len());
//     if outputs_ref.is_empty() {
//       txn.del(&key);
//     } else {
//       txn.put(&key, outputs_ref);
//     }
//     Some(res)
//   }

//   fn delayed_output_keys() -> Vec<u8> {
//     Self::multisigs_key(b"delayed_outputs", [])
//   }
//   pub fn save_delayed_output(txn: &mut D::Transaction<'_>, instruction: InInstructionWithBalance) {
//     let key = Self::delayed_output_keys();
//     let mut existing = txn.get(&key).unwrap_or(vec![]);
//     existing.extend(instruction.encode());
//     txn.put(key, existing);
//   }
//   pub fn take_delayed_outputs(txn: &mut D::Transaction<'_>) -> Vec<InInstructionWithBalance> {
//     let key = Self::delayed_output_keys();

//     let Some(outputs) = txn.get(&key) else { return vec![] };
//     txn.del(key);

//     let mut outputs_ref = outputs.as_slice();
//     let mut res = vec![];
//     while !outputs_ref.is_empty() {
//       res.push(InInstructionWithBalance::decode(&mut outputs_ref).unwrap());
//     }
//     res
//   }
// }
