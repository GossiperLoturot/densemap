//! # densemap
//!
//! This library provides a collection `DenseMap` that are permanently accessible by unique keys and fast
//! iterable. A key is generated upon insertion and can be used to access any element. Inserts,
//! removes, and gets run in constant time, and iteration has the same performance as `Vec`. Also
//! `DenseMap` reduces memory usage by reusing removed areas.
//!
//! # Examples
//!
//! ```
//! use densemap::{DenseMap, Key};
//!
//! // Creates a new dense map and inserts some elements.
//! let mut densemap = DenseMap::new();
//! let key_of_alice = densemap.insert("alice");
//! let key_of_bob = densemap.insert("bob");
//!
//! // Gets an element.
//! assert_eq!(densemap.get(key_of_alice), Some(&"alice"));
//!
//! // Removes an element.
//! assert_eq!(densemap.remove(key_of_alice), Some("alice"));
//! let key_of_charlie = densemap.insert("charlie");
//!
//! // Keys are unique and permanently accessible.
//! assert_eq!(densemap.get(key_of_alice), None);
//!
//! // Iterates all elements.
//! for value in densemap.values() {
//!     println!("{value}");
//! }
//! ```
//!
//! # Differences from other libraries
//!
//! This library is similar to `slotmap::DenseSlotMap`, but it has some differences.
//! `DenseMap` has a performance advantage due to reduced overhead. Also this library simply provides
//! only a collection `DenseMap`.
//!
//! # Benchmarks
//!
//! The performance measurement results for inserts, removes, reinserts, and iterates on the
//! collections of `std-1.72.1`. `slab-0.4.9`, `slotmap-1.0.6`, and `densemap-0.1.0` are shown
//! below table. The results are measured by using `criterion` on WSL.
//!
//! | collection | inserts | removes | reinserts | iterates |
//! |:----------:|:-------:|:-------:|:---------:|:--------:|
//! | std::vec::Vec | 16.367 | 7.0338μs | 10.438μs | 3.6754μs |
//! | std::collections::HashMap | 351.25μs | 187.99μs | 174.97μs | 14.617μs |
//! | slab::Slab | 17.728μs | 17.952μs | 26.207μs | 4.9409μs |
//! | slotmap::SlotMap | 49.043μs | 29.594μs | 48.153μs | 22.566μs |
//! | slotmap::HopSlotMap | 46.897μs | 126.29μs | 67.884μs | 24.349μs |
//! | slotmap::DenseSlotMap | 63.195μs | 62.308μs | 67.072μs | 5.2833μs |
//! | densemap::DenseMap | 40.357μs | 24.969μs | 47.280μs | 3.6269μs |

pub mod densemap;

#[cfg(test)]
mod test;

#[doc(inline)]
pub use densemap::{DenseMap, Key};
