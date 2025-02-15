use std::sync::Arc;

use sp_core::{Encode, Pair};
use sp_keyring::Sr25519Keyring;
use sp_inherents::InherentData;

use sp_runtime::OpaqueExtrinsic;

use sc_cli::Result;
use sc_client_api::BlockBackend;

use serai_runtime::{
  VERSION, BlockHashCount,
  system::{self, Call as SystemCall},
  transaction_payment, RuntimeCall, UncheckedExtrinsic, SignedPayload, Runtime,
};

use crate::service::FullClient;

pub struct RemarkBuilder {
  client: Arc<FullClient>,
}

impl RemarkBuilder {
  pub fn new(client: Arc<FullClient>) -> Self {
    Self { client }
  }
}

impl frame_benchmarking_cli::ExtrinsicBuilder for RemarkBuilder {
  fn pallet(&self) -> &str {
    "system"
  }
  fn extrinsic(&self) -> &str {
    "remark"
  }

  fn build(&self, nonce: u32) -> std::result::Result<OpaqueExtrinsic, &'static str> {
    Ok(OpaqueExtrinsic::from(create_benchmark_extrinsic(
      self.client.as_ref(),
      Sr25519Keyring::Bob.pair(),
      SystemCall::remark { remark: vec![] }.into(),
      nonce,
    )))
  }
}

pub fn create_benchmark_extrinsic(
  client: &FullClient,
  sender: sp_core::sr25519::Pair,
  call: RuntimeCall,
  nonce: u32,
) -> UncheckedExtrinsic {
  let extra = (
    system::CheckNonZeroSender::<Runtime>::new(),
    system::CheckSpecVersion::<Runtime>::new(),
    system::CheckTxVersion::<Runtime>::new(),
    system::CheckGenesis::<Runtime>::new(),
    system::CheckEra::<Runtime>::from(sp_runtime::generic::Era::mortal(
      BlockHashCount::get().checked_next_power_of_two().map(|c| c / 2).unwrap_or(2),
      client.chain_info().best_number,
    )),
    system::CheckNonce::<Runtime>::from(nonce),
    system::CheckWeight::<Runtime>::new(),
    transaction_payment::ChargeTransactionPayment::<Runtime>::from(0),
  );

  UncheckedExtrinsic::new_signed(
    call.clone(),
    sender.public().into(),
    SignedPayload::from_raw(
      call,
      extra.clone(),
      (
        (),
        VERSION.spec_version,
        VERSION.transaction_version,
        client.block_hash(0).ok().flatten().unwrap(),
        client.chain_info().best_hash,
        (),
        (),
        (),
      ),
    )
    .using_encoded(|e| sender.sign(e)),
    extra,
  )
}

pub fn inherent_benchmark_data() -> Result<InherentData> {
  Ok(InherentData::new())
}
