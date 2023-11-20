use core::marker::PhantomData;
use std::{
  sync::Arc,
  io::Read,
  time::Duration,
  collections::{VecDeque, HashSet, HashMap},
};

use ciphersuite::group::GroupEncoding;
use frost::curve::Ciphersuite;

use log::{info, debug, warn};
use serai_db::create_db;
use tokio::{
  sync::{RwLockReadGuard, RwLockWriteGuard, RwLock, mpsc},
  time::sleep,
};

use scale::Encode;
use crate::{
  Get, DbTxn, Db,
  networks::{Output, Transaction, EventualitiesTracker, Block, Network},
};

#[derive(Clone, Debug)]
pub enum ScannerEvent<N: Network> {
  // Block scanned
  Block { is_retirement_block: bool, block: <N::Block as Block<N>>::Id, outputs: Vec<N::Output> },
  // Eventuality completion found on-chain
  Completed(Vec<u8>, usize, [u8; 32], N::Transaction),
}

pub type ScannerEventChannel<N> = mpsc::UnboundedReceiver<ScannerEvent<N>>;

create_db!(
  ScannerDb {
    BlockKeyDb: (number: u64) -> Vec<u8>,
    BlockNumberKeyDb: (id: Vec<u8>) -> u64,
    KeysDb: () -> Vec<u8>,
    SeenDb: (id: Vec<u8>) -> Vec<u8>,
    OutputsDb: (block: Vec<u8>) -> Vec<u8>,
    ScannedBlocksDb: () -> u64,
    RetirementBlocksDb: (key: Vec<u8>) -> u64
  }
);

impl BlockKeyDb {

  fn save_block<N: Network>(txn: &mut impl DbTxn, number: usize, id: &<N::Block as Block<N>>::Id) {
    Self::set(
      txn,
      u64::try_from(number).unwrap(),
      &BlockNumberKeyDb::to_block_number_key::<N>(id)
    );
    BlockNumberKeyDb::set(
      txn,
      BlockNumberKeyDb::to_block_number_key::<N>(id),
      &u64::try_from(number).unwrap()
    );
  }

  fn block<N: Network>(getter: &impl Get, number: usize) -> Option<<N::Block as Block<N>>::Id> {
    Self::get(getter, number.try_into().unwrap()).map(|bytes| {
      let mut res = <N::Block as Block<N>>::Id::default();
      res.as_mut().copy_from_slice(&bytes);
      res
    })
  }
}

impl BlockNumberKeyDb {
  fn to_block_number_key<N: Network>(id: &<N::Block as Block<N>>::Id) -> Vec<u8> {
    id.as_ref().into()
  }

  fn block_number<N: Network>(getter: &impl Get, id: &<N::Block as Block<N>>::Id) -> Option<usize> {
    let key = Self::to_block_number_key::<N>(id);
    Self::get(getter, key).map(|number| usize::try_from(number).unwrap())  
  }
}

impl KeysDb {
  fn register_key<N: Network>(
    txn: &mut impl DbTxn,
    activation_number: usize,
    key: <N::Curve as Ciphersuite>::G,
  ) {
    let mut keys = Self::get(txn).unwrap_or_default();
    let key_bytes = key.to_bytes();
    let key_len = key_bytes.as_ref().len();
    assert_eq!(keys.len() % (8 + key_len), 0);

    // Sanity check this key isn't already present
    let mut i = 0;
    while i < keys.len() {
      if &keys[(i + 8) .. ((i + 8) + key_len)] == key_bytes.as_ref() {
        panic!("adding {} as a key yet it was already present", hex::encode(key_bytes));
      }
      i += 8 + key_len;
    }

    keys.extend(u64::try_from(activation_number).unwrap().to_le_bytes());
    keys.extend(key_bytes.as_ref());
    Self::set(txn, &keys);
  }

  fn keys<N: Network>(getter: &impl Get) -> Vec<(usize, <N::Curve as Ciphersuite>::G)> {
    let bytes_vec = Self::get(getter).unwrap_or_default();
    let mut bytes: &[u8] = bytes_vec.as_ref();

    // Assumes keys will be 32 bytes when calculating the capacity
    // If keys are larger, this may allocate more memory than needed
    // If keys are smaller, this may require additional allocations
    // Either are fine
    let mut res = Vec::with_capacity(bytes.len() / (8 + 32));
    while !bytes.is_empty() {
      let mut activation_number = [0; 8];
      bytes.read_exact(&mut activation_number).unwrap();
      res.push((u64::from_le_bytes(activation_number).try_into().unwrap(), N::Curve::read_G(&mut bytes).unwrap()));
    }
    res
  }

  fn retire_key<N: Network>(txn: &mut impl DbTxn) {
    let keys = Self::keys::<N>(txn);
    assert_eq!(keys.len(), 2);
    txn.del(Self::key());
    Self::register_key::<N>(txn, keys[1].0, keys[1].1);
  }
}

impl SeenDb {
  fn to_seen_key<N: Network>(id: &<N::Output as Output<N>>::Id) -> Vec<u8> {
    id.as_ref().into()
  }

  fn seen<N: Network>(getter: &impl Get, id: &<N::Output as Output<N>>::Id) -> bool {
    Self::get(getter, Self::to_seen_key::<N>(id)).is_some()
  }
}

impl OutputsDb {
  fn to_outputs_key<N: Network>(block: &<N::Block as Block<N>>::Id) -> Vec<u8> {
    block.as_ref().into()
  }

  fn save_outputs<N: Network>(
    txn: &mut impl DbTxn,
    block: &<N::Block as Block<N>>::Id,
    outputs: &[N::Output],
  ) {
    let mut bytes = Vec::with_capacity(outputs.len() * 64);
    for output in outputs {
      output.write(&mut bytes).unwrap();
    }
    Self::set(txn, Self::to_outputs_key::<N>(block), &bytes);
  }

  fn outputs<N: Network>(
    txn: &impl DbTxn,
    block: &<N::Block as Block<N>>::Id,
  ) -> Option<Vec<N::Output>> {
    let bytes_vec = Self::get(txn, Self::to_outputs_key::<N>(block))?;
    let mut bytes: &[u8] = bytes_vec.as_ref();

    let mut res = vec![];
    while !bytes.is_empty() {
      res.push(N::Output::read(&mut bytes).unwrap());
    }
    Some(res)
  }
}

impl ScannedBlocksDb {
  fn save_scanned_block<N: Network>(txn: &mut impl DbTxn, block: usize) -> Vec<N::Output> {
    let id = BlockKeyDb::block::<N>(txn, block);
    let outputs = id.as_ref().and_then(|id| OutputsDb::outputs::<N>(txn, id)).unwrap_or_default();
    
    // Mark all the outputs from this block as seen
    for output in &outputs {
      SeenDb::set(txn, SeenDb::to_seen_key::<N>(&output.id()), b"");
    }
    Self::set(txn, &u64::try_from(block).unwrap());

    // Return this block's outputs so they can be pruned from the RAM cache
    outputs
  }

  fn latest_scanned_block(getter: &impl Get) -> Option<usize> {
    Self::get(getter)
      .map(|number| usize::try_from(number).unwrap())
  }
}

impl RetirementBlocksDb {
  fn to_retirement_block_key<N: Network>(key: &<N::Curve as Ciphersuite>::G) -> Vec<u8> {
    key.to_bytes().as_ref().to_vec()
  }

  fn save_retirement_block<N: Network>(
    txn: &mut impl DbTxn,
    key: &<N::Curve as Ciphersuite>::G,
    block: usize,
  ) {
    Self::set(txn, Self::to_retirement_block_key::<N>(key), &u64::try_from(block).unwrap());
  }

  fn retirement_block<N: Network>(getter: &impl Get, key: &<N::Curve as Ciphersuite>::G) -> Option<usize> {
    Self::get(getter, Self::to_retirement_block_key::<N>(key)).map(|number| usize::try_from(number).unwrap())  
  }
}


/// The Scanner emits events relating to the blockchain, notably received outputs.
///
/// It WILL NOT fail to emit an event, even if it reboots at selected moments.
///
/// It MAY fire the same event multiple times.
#[derive(Debug)]
pub struct Scanner<N: Network, D: Db> {
  _db: PhantomData<D>,

  keys: Vec<(usize, <N::Curve as Ciphersuite>::G)>,

  eventualities: HashMap<Vec<u8>, EventualitiesTracker<N::Eventuality>>,

  ram_scanned: Option<usize>,
  ram_outputs: HashSet<Vec<u8>>,

  need_ack: VecDeque<usize>,

  events: mpsc::UnboundedSender<ScannerEvent<N>>,
}

#[derive(Clone, Debug)]
struct ScannerHold<N: Network, D: Db> {
  scanner: Arc<RwLock<Option<Scanner<N, D>>>>,
}
impl<N: Network, D: Db> ScannerHold<N, D> {
  async fn read(&self) -> RwLockReadGuard<'_, Option<Scanner<N, D>>> {
    loop {
      let lock = self.scanner.read().await;
      if lock.is_none() {
        drop(lock);
        tokio::task::yield_now().await;
        continue;
      }
      return lock;
    }
  }
  async fn write(&self) -> RwLockWriteGuard<'_, Option<Scanner<N, D>>> {
    loop {
      let lock = self.scanner.write().await;
      if lock.is_none() {
        drop(lock);
        tokio::task::yield_now().await;
        continue;
      }
      return lock;
    }
  }
  // This is safe to not check if something else already acquired the Scanner as the only caller is
  // sequential.
  async fn long_term_acquire(&self) -> Scanner<N, D> {
    self.scanner.write().await.take().unwrap()
  }
  async fn restore(&self, scanner: Scanner<N, D>) {
    let _ = self.scanner.write().await.insert(scanner);
  }
}

#[derive(Debug)]
pub struct ScannerHandle<N: Network, D: Db> {
  scanner: ScannerHold<N, D>,
  held_scanner: Option<Scanner<N, D>>,
  pub events: ScannerEventChannel<N>,
  pub multisig_completed: mpsc::UnboundedSender<bool>,
}

impl<N: Network, D: Db> ScannerHandle<N, D> {
  pub async fn ram_scanned(&self) -> usize {
    self.scanner.read().await.as_ref().unwrap().ram_scanned.unwrap_or(0)
  }

  /// Register a key to scan for.
  pub async fn register_key(
    &mut self,
    txn: &mut D::Transaction<'_>,
    activation_number: usize,
    key: <N::Curve as Ciphersuite>::G,
  ) {
    let mut scanner_lock = self.scanner.write().await;
    let scanner = scanner_lock.as_mut().unwrap();
    assert!(
      activation_number > scanner.ram_scanned.unwrap_or(0),
      "activation block of new keys was already scanned",
    );

    info!("Registering key {} in scanner at {activation_number}", hex::encode(key.to_bytes()));

    if scanner.keys.is_empty() {
      assert!(scanner.ram_scanned.is_none());
      scanner.ram_scanned = Some(activation_number);
      assert!(ScannedBlocksDb::save_scanned_block::<N>(txn, activation_number).is_empty());
    }

    KeysDb::register_key::<N>(txn, activation_number, key);
    scanner.keys.push((activation_number, key));
    #[cfg(not(test))] // TODO: A test violates this. Improve the test with a better flow
    assert!(scanner.keys.len() <= 2);

    scanner.eventualities.insert(key.to_bytes().as_ref().to_vec(), EventualitiesTracker::new());
  }

  pub fn db_scanned<G: Get>(getter: &G) -> Option<usize> {
    ScannedBlocksDb::get(getter).map(|number| usize::try_from(number).unwrap())
  }

  // This perform a database read which isn't safe with regards to if the value is set or not
  // It may be set, when it isn't expected to be set, or not set, when it is expected to be set
  // Since the value is static, if it's set, it's correctly set
  pub fn block_number(getter: &impl Get, id: &<N::Block as Block<N>>::Id) -> Option<usize> {
    BlockNumberKeyDb::block_number::<N>(getter, id)
  }

  /// Acknowledge having handled a block.
  ///
  /// Creates a lock over the Scanner, preventing its independent scanning operations until
  /// released.
  ///
  /// This must only be called on blocks which have been scanned in-memory.
  pub async fn ack_block(
    &mut self,
    txn: &mut D::Transaction<'_>,
    id: <N::Block as Block<N>>::Id,
  ) -> (bool, Vec<N::Output>) {
    debug!("block {} acknowledged", hex::encode(&id));

    let mut scanner = self.scanner.long_term_acquire().await;

    // Get the number for this block
    let number = BlockNumberKeyDb::block_number::<N>(txn, &id)
      .expect("main loop trying to operate on data we haven't scanned");
    log::trace!("block {} was {number}", hex::encode(&id));

    let outputs = ScannedBlocksDb::save_scanned_block::<N>(txn, number);
    // This has a race condition if we try to ack a block we scanned on a prior boot, and we have
    // yet to scan it on this boot
    assert!(number <= scanner.ram_scanned.unwrap());
    for output in &outputs {
      assert!(scanner.ram_outputs.remove(output.id().as_ref()));
    }

    assert_eq!(scanner.need_ack.pop_front().unwrap(), number);

    self.held_scanner = Some(scanner);

    // Load the key from the DB, as it will have already been removed from RAM if retired
    let key = KeysDb::keys::<N>(txn)[0].1;
    let is_retirement_block = RetirementBlocksDb::retirement_block::<N>(txn, &key) == Some(number);
    if is_retirement_block {
      KeysDb::retire_key::<N>(txn);
    }
    (is_retirement_block, outputs)
  }

  pub async fn register_eventuality(
    &mut self,
    key: &[u8],
    block_number: usize,
    id: [u8; 32],
    eventuality: N::Eventuality,
  ) {
    let mut lock;
    // We won't use held_scanner if we're re-registering on boot
    (if let Some(scanner) = self.held_scanner.as_mut() {
      scanner
    } else {
      lock = Some(self.scanner.write().await);
      lock.as_mut().unwrap().as_mut().unwrap()
    })
    .eventualities
    .get_mut(key)
    .unwrap()
    .register(block_number as usize, id, eventuality)
  }

  pub async fn release_lock(&mut self) {
    self.scanner.restore(self.held_scanner.take().unwrap()).await
  }
}

impl<N: Network, D: Db> Scanner<N, D> {
  #[allow(clippy::type_complexity, clippy::new_ret_no_self)]
  pub fn new(
    network: N,
    db: D,
  ) -> (ScannerHandle<N, D>, Vec<(usize, <N::Curve as Ciphersuite>::G)>) {
    let (events_send, events_recv) = mpsc::unbounded_channel();
    let (multisig_completed_send, multisig_completed_recv) = mpsc::unbounded_channel();

    let keys = KeysDb::keys::<N>(&db);
    let mut eventualities = HashMap::new();
    for key in &keys {
      eventualities.insert(key.1.to_bytes().as_ref().to_vec(), EventualitiesTracker::new());
    }

    let ram_scanned = ScannedBlocksDb::latest_scanned_block(&db);

    let scanner = ScannerHold {
      scanner: Arc::new(RwLock::new(Some(Scanner {
        _db: PhantomData,

        keys: keys.clone(),

        eventualities,

        ram_scanned,
        ram_outputs: HashSet::new(),

        need_ack: VecDeque::new(),

        events: events_send,
      }))),
    };
    tokio::spawn(Scanner::run(db, network, scanner.clone(), multisig_completed_recv));

    (
      ScannerHandle {
        scanner,
        held_scanner: None,
        events: events_recv,
        multisig_completed: multisig_completed_send,
      },
      keys,
    )
  }

  async fn emit(&mut self, event: ScannerEvent<N>) -> bool {
    if self.events.send(event).is_err() {
      info!("Scanner handler was dropped. Shutting down?");
      return false;
    }
    true
  }

  // An async function, to be spawned on a task, to discover and report outputs
  async fn run(
    mut db: D,
    network: N,
    scanner_hold: ScannerHold<N, D>,
    mut multisig_completed: mpsc::UnboundedReceiver<bool>,
  ) {
    loop {
      let (ram_scanned, latest_block_to_scan) = {
        // Sleep 5 seconds to prevent hammering the node/scanner lock
        sleep(Duration::from_secs(5)).await;

        let ram_scanned = {
          let scanner_lock = scanner_hold.read().await;
          let scanner = scanner_lock.as_ref().unwrap();

          // If we're not scanning for keys yet, wait until we are
          if scanner.keys.is_empty() {
            continue;
          }

          let ram_scanned = scanner.ram_scanned.unwrap();
          // If a Batch has taken too long to be published, start waiting until it is before
          // continuing scanning
          // Solves a race condition around multisig rotation, documented in the relevant doc
          // and demonstrated with mini
          if let Some(needing_ack) = scanner.need_ack.front() {
            let next = ram_scanned + 1;
            let limit = needing_ack + N::CONFIRMATIONS;
            assert!(next <= limit);
            if next == limit {
              continue;
            }
          };

          ram_scanned
        };

        (
          ram_scanned,
          loop {
            break match network.get_latest_block_number().await {
              // Only scan confirmed blocks, which we consider effectively finalized
              // CONFIRMATIONS - 1 as whatever's in the latest block already has 1 confirm
              Ok(latest) => latest.saturating_sub(N::CONFIRMATIONS.saturating_sub(1)),
              Err(_) => {
                warn!("couldn't get latest block number");
                sleep(Duration::from_secs(60)).await;
                continue;
              }
            };
          },
        )
      };

      for block_being_scanned in (ram_scanned + 1) ..= latest_block_to_scan {
        // Redo the checks for if we're too far ahead
        {
          let needing_ack = {
            let scanner_lock = scanner_hold.read().await;
            let scanner = scanner_lock.as_ref().unwrap();
            scanner.need_ack.front().cloned()
          };

          if let Some(needing_ack) = needing_ack {
            let limit = needing_ack + N::CONFIRMATIONS;
            assert!(block_being_scanned <= limit);
            if block_being_scanned == limit {
              break;
            }
          }
        }

        let block = match network.get_block(block_being_scanned as usize).await {
          Ok(block) => block,
          Err(_) => {
            warn!("couldn't get block {block_being_scanned}");
            break;
          }
        };
        let block_id = block.id();

        info!("scanning block: {} ({block_being_scanned})", hex::encode(&block_id));

        // These DB calls are safe, despite not having a txn, since they're static values
        // There's no issue if they're written in advance of expected (such as on reboot)
        // They're also only expected here
        if let Some(id) = BlockKeyDb::block::<N>(&db, block_being_scanned) {
          if id != block_id {
            panic!("reorg'd from finalized {} to {}", hex::encode(id), hex::encode(block_id));
          }
        } else {
          // TODO: Move this to an unwrap
          if let Some(id) = BlockKeyDb::block::<N>(&db, block_being_scanned.saturating_sub(1)) {
            if id != block.parent() {
              panic!(
                "block {} doesn't build off expected parent {}",
                hex::encode(block_id),
                hex::encode(id),
              );
            }
          }

          let mut txn = db.txn();
          BlockKeyDb::save_block::<N>(&mut txn, block_being_scanned, &block_id);
          txn.commit();
        }

        // Scan new blocks
        // TODO: This lock acquisition may be long-lived...
        let mut scanner_lock = scanner_hold.write().await;
        let scanner = scanner_lock.as_mut().unwrap();

        let mut has_activation = false;
        let mut outputs = vec![];
        let mut completion_block_numbers = vec![];
        for (activation_number, key) in scanner.keys.clone() {
          if activation_number > block_being_scanned {
            continue;
          }

          if activation_number == block_being_scanned {
            has_activation = true;
          }

          let key_vec = key.to_bytes().as_ref().to_vec();

          // TODO: These lines are the ones which will cause a really long-lived lock acquisiton
          for output in network.get_outputs(&block, key).await {
            assert_eq!(output.key(), key);
            if output.balance().amount.0 >= N::DUST {
              outputs.push(output);
            }
          }

          for (id, (block_number, tx)) in network
            .get_eventuality_completions(scanner.eventualities.get_mut(&key_vec).unwrap(), &block)
            .await
          {
            info!(
              "eventuality {} resolved by {}, as found on chain",
              hex::encode(id),
              hex::encode(&tx.id())
            );

            completion_block_numbers.push(block_number);
            // This must be before the mission of ScannerEvent::Block, per commentary in mod.rs
            if !scanner.emit(ScannerEvent::Completed(key_vec.clone(), block_number, id, tx)).await {
              return;
            }
          }
        }

        // Panic if we've already seen these outputs
        for output in &outputs {
          let id = output.id();
          info!(
            "block {} had output {} worth {:?}",
            hex::encode(&block_id),
            hex::encode(&id),
            output.balance(),
          );

          // On Bitcoin, the output ID should be unique for a given chain
          // On Monero, it's trivial to make an output sharing an ID with another
          // We should only scan outputs with valid IDs however, which will be unique

          /*
            The safety of this code must satisfy the following conditions:
            1) seen is not set for the first occurrence
            2) seen is set for any future occurrence

            seen is only written to after this code completes. Accordingly, it cannot be set
            before the first occurrence UNLESSS it's set, yet the last scanned block isn't.
            They are both written in the same database transaction, preventing this.

            As for future occurrences, the RAM entry ensures they're handled properly even if
            the database has yet to be set.

            On reboot, which will clear the RAM, if seen wasn't set, neither was latest scanned
            block. Accordingly, this will scan from some prior block, re-populating the RAM.

            If seen was set, then this will be successfully read.

            There's also no concern ram_outputs was pruned, yet seen wasn't set, as pruning
            from ram_outputs will acquire a write lock (preventing this code from acquiring
            its own write lock and running), and during its holding of the write lock, it
            commits the transaction setting seen and the latest scanned block.

            This last case isn't true. Committing seen/latest_scanned_block happens after
            relinquishing the write lock.

            TODO2: Only update ram_outputs after committing the TXN in question.
          */
          let seen = SeenDb::seen::<N>(&db, &id);
          let id = id.as_ref().to_vec();
          if seen || scanner.ram_outputs.contains(&id) {
            panic!("scanned an output multiple times");
          }
          scanner.ram_outputs.insert(id);
        }

        // We could remove this, if instead of doing the first block which passed
        // requirements + CONFIRMATIONS, we simply emitted an event for every block where
        // `number % CONFIRMATIONS == 0` (once at the final stage for the existing multisig)
        // There's no need at this point, yet the latter may be more suitable for modeling...
        async fn check_multisig_completed<N: Network, D: Db>(
          db: &mut D,
          multisig_completed: &mut mpsc::UnboundedReceiver<bool>,
          block_number: usize,
        ) -> bool {
          match multisig_completed.recv().await {
            None => {
              info!("Scanner handler was dropped. Shutting down?");
              false
            }
            Some(completed) => {
              // Set the retirement block as block_number + CONFIRMATIONS
              if completed {
                let mut txn = db.txn();
                // The retiring key is the earliest one still around
                let retiring_key = KeysDb::keys::<N>(&txn)[0].1;
                // This value is static w.r.t. the key
                RetirementBlocksDb::save_retirement_block::<N>(
                  &mut txn,
                  &retiring_key,
                  block_number + N::CONFIRMATIONS,
                );
                txn.commit();
              }
              true
            }
          }
        }

        drop(scanner_lock);
        // Now that we've dropped the Scanner lock, we need to handle the multisig_completed
        // channel before we decide if this block should be fired or not
        // (holding the Scanner risks a deadlock)
        for block_number in completion_block_numbers {
          if !check_multisig_completed::<N, _>(&mut db, &mut multisig_completed, block_number.try_into().unwrap()).await
          {
            return;
          };
        }

        // Reacquire the scanner
        let mut scanner_lock = scanner_hold.write().await;
        let scanner = scanner_lock.as_mut().unwrap();

        // Only emit an event if any of the following is true:
        // - This is an activation block
        // - This is a retirement block
        // - There's outputs
        // as only those blocks are meaningful and warrant obtaining synchrony over
        let is_retirement_block =
        RetirementBlocksDb::retirement_block::<N>(&db, &scanner.keys[0].1) == Some(block_being_scanned);
        let sent_block = if has_activation || is_retirement_block || (!outputs.is_empty()) {
          // Save the outputs to disk
          let mut txn = db.txn();
          OutputsDb::save_outputs::<N>(&mut txn, &block_id, &outputs);
          txn.commit();

          // Send all outputs
          if !scanner
            .emit(ScannerEvent::Block { is_retirement_block, block: block_id, outputs })
            .await
          {
            return;
          }

          // Since we're creating a Batch, mark it as needing ack
          scanner.need_ack.push_back(block_being_scanned);
          true
        } else {
          false
        };

        // Remove it from memory
        if is_retirement_block {
          let retired = scanner.keys.remove(0).1;
          scanner.eventualities.remove(retired.to_bytes().as_ref());
        }

        // Update ram_scanned
        scanner.ram_scanned = Some(block_being_scanned);

        drop(scanner_lock);
        // If we sent a Block event, once again check multisig_completed
        if sent_block &&
          (!check_multisig_completed::<N, _>(
            &mut db,
            &mut multisig_completed,
            block_being_scanned,
          )
          .await)
        {
          return;
        }
      }
    }
  }
}
