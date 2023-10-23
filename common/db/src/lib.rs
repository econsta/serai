mod mem;
pub use mem::*;
mod db_macro;
pub use db_macro::*;

#[cfg(feature = "rocksdb")]
mod rocks;
#[cfg(feature = "rocksdb")]
pub use rocks::{RocksDB, new_rocksdb};

/// An object implementing get.
pub trait Get {
  fn get(&self, key: impl AsRef<[u8]>) -> Option<Vec<u8>>;
}

/// An atomic database operation.
#[must_use]
pub trait DbTxn: Send + Get {
  fn put(&mut self, key: impl AsRef<[u8]>, value: impl AsRef<[u8]>);
  fn del(&mut self, key: impl AsRef<[u8]>);
  fn commit(self);
}

/// A database supporting atomic operations.
pub trait Db: 'static + Send + Sync + Clone + Get {
  type Transaction<'a>: DbTxn;
  
  fn txn(&mut self) -> Self::Transaction<'_>;
}
