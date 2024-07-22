use alloc::{
    collections,
    vec::{self, Vec},
};
use core::{fmt, iter, ops, slice};

/// An index of sparse layer and mode at the position.
///
/// if `generation` is an even number, the key is in occupied mode, otherwise it is
/// in vacant mode. Occupied mode means that the correspondence between `idx_or_next` and
/// the element in dense layer, which is pointed to by `idx_or_next`, are available. Vacant
/// mode is other than occupied mode.
#[derive(Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
enum SparseIdx {
    Vacant { next: Option<u32> },
    Occupied { index: u32 },
}

/// A contiguous array with sparse index, written as `DenseMap<T>`, short for 'dense map'.
///
/// # Examples
///
/// ```
/// use densemap::DenseMap;
///
/// let mut densemap = DenseMap::new();
/// let key = densemap.insert(0);
/// assert_eq!(densemap.get(key), Some(&0));
/// ```
///
/// For more information see
/// [Crate documentation](crate).
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct DenseMap<T> {
    /// A next free index of sparse layer.
    next: Option<u32>,
    /// A correspondence to dense layer from sparse layer.
    entries: Vec<SparseIdx>,

    /// A correspondence to sparse layer from dense layer.
    keys: Vec<u32>,
    values: Vec<T>,
}

impl<T> DenseMap<T> {
    /// Constructs a new, empty `DenseMap<T>`.
    ///
    /// The dense map will not allocate until elements are inserted onto it.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let densemap: DenseMap<i32> = DenseMap::new();
    /// assert_eq!(densemap.len(), 0);
    /// ```
    #[inline]
    pub const fn new() -> DenseMap<T> {
        DenseMap {
            next: None,
            entries: Vec::new(),
            keys: Vec::new(),
            values: Vec::new(),
        }
    }

    /// Constructs a new, empty `DenseMap<T>` with at least the specified capacity.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let densemap: DenseMap<i32> = DenseMap::with_capacity(10, 2);
    /// assert_eq!(densemap.len(), 0);
    /// let (sparse, dense) = densemap.capacity();
    /// assert!(10 <= sparse && 2 <= dense);
    /// ```
    #[inline]
    pub fn with_capacity(sparse_capacity: usize, dense_capacity: usize) -> DenseMap<T> {
        DenseMap {
            next: None,
            entries: Vec::with_capacity(sparse_capacity),
            keys: Vec::with_capacity(dense_capacity),
            values: Vec::with_capacity(dense_capacity),
        }
    }

    /// Returns the total number of elements the dense map can hold without
    /// reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::with_capacity(10, 2);
    /// densemap.insert(42);
    /// let (sparse, dense) = densemap.capacity();
    /// assert!(10 <= sparse && 2 <= dense);
    /// ```
    #[inline]
    pub fn capacity(&self) -> (usize, usize) {
        let sparse = self.entries.capacity();
        let dense = self.keys.capacity();
        (sparse, dense)
    }

    /// Reserves capacity for at least `additional` more elements to be inserted in the `DenseMap`.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX`.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    /// let mut densemap = DenseMap::new();
    /// densemap.reserve(10, 2);
    /// densemap.insert(1);
    /// ```
    #[inline]
    pub fn reserve(&mut self, sparse_additional: usize, dense_additional: usize) {
        self.entries.reserve(sparse_additional);
        self.keys.reserve(dense_additional);
        self.values.reserve(dense_additional);
    }
    /// Tries to reserves capacity for at least `additional` more elements to be inserted
    /// in the `DenseMap`.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX`.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    /// let mut densemap = DenseMap::new();
    /// densemap.try_reserve(10, 2).expect("can't reserve capacity");
    /// densemap.insert(1);
    /// ```
    #[inline]
    pub fn try_reserve(
        &mut self,
        sparse_additional: usize,
        dense_additional: usize,
    ) -> Result<(), collections::TryReserveError> {
        self.entries.try_reserve(sparse_additional)?;
        self.keys.try_reserve(dense_additional)?;
        self.values.try_reserve(dense_additional)?;
        Ok(())
    }

    /// Shrinks the capacity of the dense map as much as possible.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::with_capacity(100, 100);
    /// densemap.insert(3);
    /// densemap.insert(4);
    /// let (sparse, dense) = densemap.capacity();
    /// assert!(100 <= sparse && 100 <= dense);
    /// densemap.shrink_to_fit();
    /// let (sparse, dense) = densemap.capacity();
    /// assert!(2 <= sparse && 2 <= dense);
    /// ```
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.entries.shrink_to_fit();
        self.keys.shrink_to_fit();
        self.values.shrink_to_fit();
    }

    /// Shrinks the capacity of the map with a lower limit.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::with_capacity(100, 100);
    /// densemap.insert(3);
    /// densemap.insert(4);
    /// let (sparse, dense) = densemap.capacity();
    /// assert!(100 <= sparse && 100 <= dense);
    /// densemap.shrink_to(10, 10);
    /// let (sparse, dense) = densemap.capacity();
    /// assert!(10 <= sparse && 10 <= dense);
    /// ```
    #[inline]
    pub fn shrink_to(&mut self, sparse_capacity: usize, dense_capacity: usize) {
        self.entries.shrink_to(sparse_capacity);
        self.keys.shrink_to(dense_capacity);
        self.values.shrink_to(dense_capacity);
    }

    /// An iterator visiting all keys in arbitrary order.
    /// The iterator element type is `&'a Key`.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::new();
    /// densemap.insert(1);
    /// let keys = densemap.keys();
    /// ```
    #[inline]
    pub fn keys(&self) -> Keys<'_> {
        Keys {
            inner: self.keys.iter(),
        }
    }

    /// Creates a consuming iterator visiting all the keys in arbitrary order.
    /// The dense map cannot be used after calling this.
    /// The iterator element type is `Key`.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::new();
    /// densemap.insert(1);
    /// let keys = densemap.keys();
    /// ```
    #[inline]
    pub fn into_keys(self) -> IntoKeys {
        IntoKeys {
            inner: self.keys.into_iter(),
        }
    }

    /// Extracts a slice containing the entire keys.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::new();
    /// densemap.insert(1);
    /// let key = densemap.as_key_slice();
    /// ```
    #[inline]
    pub fn as_key_slice(&self) -> &[u32] {
        self.keys.as_slice()
    }

    /// An iterator visiting all values in arbitrary order.
    /// The iterator element type is `&'a T`.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::new();
    /// densemap.insert(1);
    /// let values = densemap.values();
    /// ```
    #[inline]
    pub fn values(&self) -> Values<'_, T> {
        Values {
            inner: self.values.iter(),
        }
    }

    /// An iterator visiting all values mutably in arbitrary order.
    /// The iterator element type is `&'a mut T`.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::new();
    /// densemap.insert(1);
    /// let values = densemap.values_mut();
    /// ```
    #[inline]
    pub fn values_mut(&mut self) -> ValuesMut<'_, T> {
        ValuesMut {
            inner: self.values.iter_mut(),
        }
    }

    /// Creates a consuming iterator visiting all the values in arbitrary order.
    /// The dense map cannot be used after calling this.
    /// The iterator element type is `T`.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::new();
    /// densemap.insert(1);
    /// let values = densemap.into_values();
    /// ```
    #[inline]
    pub fn into_values(self) -> IntoValues<T> {
        IntoValues {
            inner: self.values.into_iter(),
        }
    }

    /// Extracts a slice containing the entire value.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::new();
    /// densemap.insert(1);
    /// let key = densemap.as_value_slice();
    /// ```
    #[inline]
    pub fn as_value_slice(&self) -> &[T] {
        self.values.as_slice()
    }

    /// Extracts a mutable slice of the entire value.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::new();
    /// densemap.insert(1);
    /// let key = densemap.as_value_slice();
    /// ```
    #[inline]
    pub fn as_value_mut_slice(&mut self) -> &mut [T] {
        self.values.as_mut_slice()
    }

    /// An iterator visiting all key-value pairs in arbitrary order.
    /// The iterator element type is `(&'a Key, &'a T)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::new();
    /// densemap.insert(12);
    /// densemap.insert(34);
    /// let mut iter = densemap.iter();
    /// ```
    #[inline]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            inner_keys: self.keys.iter(),
            inner_values: self.values.iter(),
        }
    }

    /// An iterator visiting all key-value pairs in arbitrary order,
    /// with mutable references to the values.
    /// The iterator element type is `(&'a Key, &'a mut T)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::new();
    /// densemap.insert(12);
    /// densemap.insert(34);
    /// let mut iter = densemap.iter();
    /// ```
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            inner_keys: self.keys.iter(),
            inner_values: self.values.iter_mut(),
        }
    }

    /// Returns the number of elements in the dense map.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::new();
    /// densemap.insert(3);
    /// assert_eq!(densemap.len(), 1);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.keys.len()
    }

    /// Returns `true` if the dense map contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::new();
    /// assert!(densemap.is_empty());
    ///
    /// densemap.insert(1);
    /// assert!(!densemap.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.keys.is_empty()
    }

    /// Clears the dense map, removing all key-value pairs as an iterator.
    /// Keeps the allocated memory for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::new();
    /// densemap.insert(3);
    /// densemap.insert(4);
    /// let iter = densemap.drain();
    #[inline]
    pub fn drain(&mut self) -> Drain<'_, T> {
        self.next = None;
        self.entries.clear();
        Drain {
            inner_keys: self.keys.drain(..),
            inner_values: self.values.drain(..),
        }
    }

    /// Clears the dense map, removing all values and index.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::new();
    /// densemap.insert(3);
    /// densemap.clear();
    /// assert!(densemap.is_empty())
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.next = None;
        self.entries.clear();
        self.keys.clear();
        self.values.clear();
    }

    /// Returns `true` if the dense map contains a value for the specified key.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::new();
    /// assert!(densemap.is_empty());
    ///
    /// let key = densemap.insert(1);
    /// assert!(densemap.contain_key(key));
    /// ```
    pub fn contain_key(&self, key: u32) -> bool {
        let entry = match self.entries.get(key as usize) {
            Some(entry) => entry,
            None => return false,
        };

        match entry {
            SparseIdx::Occupied { .. } => true,
            SparseIdx::Vacant { .. } => false,
        }
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::new();
    /// let key = densemap.insert(3);
    /// assert_eq!(densemap.get(key), Some(&3));
    /// ```
    #[inline]
    pub fn get(&self, key: u32) -> Option<&T> {
        self.get_key_value(key).map(|(_, value)| value)
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::new();
    /// let key = densemap.insert(3);
    /// let (key, value) = densemap.get_key_value(key).unwrap();
    /// ```
    pub fn get_key_value(&self, key: u32) -> Option<(&u32, &T)> {
        let entry = match self.entries.get(key as usize) {
            Some(entry) => entry,
            None => return None,
        };

        let index = *match entry {
            SparseIdx::Occupied { index } => index,
            SparseIdx::Vacant { .. } => return None,
        };

        let key = &self.keys[index as usize];
        let value = &self.values[index as usize];
        Some((key, value))
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::new();
    /// let key = densemap.insert(3);
    ///
    /// if let Some(value) = densemap.get_mut(key) {
    ///     *value = 24;
    /// }
    ///
    /// assert_eq!(densemap.get(key), Some(&24));
    /// ```
    pub fn get_mut(&mut self, key: u32) -> Option<&mut T> {
        let entry = match self.entries.get(key as usize) {
            Some(entry) => entry,
            None => return None,
        };

        let index = *match entry {
            SparseIdx::Occupied { index } => index,
            SparseIdx::Vacant { .. } => return None,
        };

        let value = &mut self.values[index as usize];
        Some(value)
    }

    /// Inserts an element to the back of collection and returns key as stable identity.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX`.
    /// Panics if a index or generation of element in the sparse layer exceeds `u32::MAX`.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::new();
    /// let key = densemap.insert(3);
    /// assert_eq!(densemap.get(key), Some(&3));
    /// ```
    #[inline]
    pub fn insert(&mut self, value: T) -> u32 {
        self.insert_with_key(|_| value)
    }

    /// Inserts a value given by `f` into the map. The key where the
    /// value will be stored is passed into `f`. This is useful to store value
    /// that contain their own key.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX`.
    /// Panics if a index or generation of element in the sparse layer exceeds `u32::MAX`.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::new();
    /// let key = densemap.insert_with_key(|key| (key, 3));
    /// assert_eq!(densemap.get(key), Some(&(key, 3)));
    /// ```
    pub fn insert_with_key<F>(&mut self, f: F) -> u32
    where
        F: FnOnce(u32) -> T,
    {
        if let Some(key) = self.next {
            let entry = match self.entries.get_mut(key as usize) {
                Some(entry) => entry,
                None => unreachable!(),
            };

            let next = *match entry {
                SparseIdx::Occupied { .. } => unreachable!(),
                SparseIdx::Vacant { next } => next,
            };

            self.next = next;

            *entry = SparseIdx::Occupied {
                index: self.keys.len() as u32,
            };
            self.keys.push(key);
            self.values.push(f(key));
            key
        } else {
            if self.entries.len() > u32::MAX as usize {
                panic!("capacity overflow");
            }

            let key = self.entries.len() as u32;

            let entry = SparseIdx::Occupied {
                index: self.keys.len() as u32,
            };

            self.entries.push(entry);
            self.keys.push(key);
            self.values.push(f(key));
            key
        }
    }

    /// Removes a key from the map, returning the value
    /// at the key if the key was previously in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::new();
    /// let key = densemap.insert(3);
    /// assert_eq!(densemap.remove(key), Some(3));
    /// ```
    #[inline]
    pub fn remove(&mut self, key: u32) -> Option<T> {
        self.remove_entry(key).map(|(_, value)| value)
    }

    /// Removes a key from the dense map, returning the stored key
    /// and value if the key was previously in the dense map.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::new();
    /// let key = densemap.insert(3);
    /// let (key, value) = densemap.remove_entry(key).unwrap();
    /// ```
    pub fn remove_entry(&mut self, key: u32) -> Option<(u32, T)> {
        let entry = match self.entries.get_mut(key as usize) {
            Some(entry) => entry,
            None => return None,
        };

        let index = *match entry {
            SparseIdx::Occupied { index } => index,
            SparseIdx::Vacant { .. } => return None,
        };

        *entry = SparseIdx::Vacant { next: self.next };

        self.next = Some(key);
        let key = self.keys.swap_remove(index as usize);
        let value = self.values.swap_remove(index as usize);

        if index < self.keys.len() as u32 {
            self.entries[self.keys[index as usize] as usize] = SparseIdx::Occupied { index };
        }

        Some((key, value))
    }
}

impl<T: Clone> Clone for DenseMap<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            next: self.next,
            entries: self.entries.clone(),
            keys: self.keys.clone(),
            values: self.values.clone(),
        }
    }
}

impl<T: PartialEq> PartialEq for DenseMap<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter()
            .all(|(key, value)| other.get(*key).map_or(false, |v| *value == *v))
    }
}

impl<T: Eq> Eq for DenseMap<T> {}

impl<T: fmt::Debug> fmt::Debug for DenseMap<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<T> Default for DenseMap<T> {
    #[inline]
    fn default() -> DenseMap<T> {
        DenseMap::new()
    }
}

impl<T> ops::Index<u32> for DenseMap<T> {
    type Output = T;

    #[inline]
    fn index(&self, key: u32) -> &T {
        self.get(key).expect("no entry found for key")
    }
}

impl<T> ops::IndexMut<u32> for DenseMap<T> {
    #[inline]
    fn index_mut(&mut self, key: u32) -> &mut T {
        self.get_mut(key).expect("no entry found for key")
    }
}

impl<'a, T> IntoIterator for &'a DenseMap<T> {
    type Item = (&'a u32, &'a T);
    type IntoIter = Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut DenseMap<T> {
    type Item = (&'a u32, &'a mut T);
    type IntoIter = IterMut<'a, T>;

    #[inline]
    fn into_iter(self) -> IterMut<'a, T> {
        self.iter_mut()
    }
}

impl<T> IntoIterator for DenseMap<T> {
    type Item = (u32, T);
    type IntoIter = IntoIter<T>;

    #[inline]
    fn into_iter(self) -> IntoIter<T> {
        IntoIter {
            inner_keys: self.keys.into_iter(),
            inner_values: self.values.into_iter(),
        }
    }
}

impl<T> Extend<T> for DenseMap<T> {
    #[inline]
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |value| {
            self.insert(value);
        });
    }
}

impl<T> FromIterator<T> for DenseMap<T> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> DenseMap<T> {
        let mut densemap = DenseMap::new();
        densemap.extend(iter);
        densemap
    }
}

impl<T, const N: usize> From<[T; N]> for DenseMap<T> {
    #[inline]
    fn from(value: [T; N]) -> DenseMap<T> {
        Self::from_iter(value)
    }
}

/// A draining iterator over the entries of a `DenseMap`.
///
/// This `struct` is created by the [`drain`] method on [`DenseMap`]. See its
/// documentation for more.
///
/// [`drain`]: DenseMap::drain
///
/// # Examples
///
/// ```
/// use densemap::DenseMap;
///
/// let mut densemap = DenseMap::new();
/// densemap.insert(1);
/// let drain = densemap.drain();
/// ```
pub struct Drain<'a, T> {
    inner_keys: vec::Drain<'a, u32>,
    inner_values: vec::Drain<'a, T>,
}

impl<T: fmt::Debug> fmt::Debug for Drain<'_, T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let keys = self.inner_keys.as_ref().iter();
        let values = self.inner_values.as_ref().iter();
        f.debug_list().entries(Iterator::zip(keys, values)).finish()
    }
}

impl<'a, T> Iterator for Drain<'a, T> {
    type Item = (u32, T);

    #[inline]
    fn next(&mut self) -> Option<(u32, T)> {
        let key = self.inner_keys.next()?;
        let value = self.inner_values.next()?;
        Some((key, value))
    }
}

impl<T> ExactSizeIterator for Drain<'_, T> {
    #[inline]
    fn len(&self) -> usize {
        self.inner_keys.len()
    }
}

impl<T> iter::FusedIterator for Drain<'_, T> {}

/// An iterator over the keys of a `DenseMap`.
///
/// This `struct` is created by the [`keys`] method on [`DenseMap`]. See its
/// documentation for more.
///
/// [`keys`]: DenseMap::keys
///
/// # Example
///
/// ```
/// use densemap::DenseMap;
///
/// let mut densemap = DenseMap::new();
/// densemap.insert(1);
/// let keys = densemap.keys();
/// ```
pub struct Keys<'a> {
    inner: slice::Iter<'a, u32>,
}

impl Clone for Keys<'_> {
    #[inline]
    fn clone(&self) -> Self {
        Keys {
            inner: self.inner.clone(),
        }
    }
}

impl fmt::Debug for Keys<'_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a> Iterator for Keys<'a> {
    type Item = &'a u32;

    #[inline]
    fn next(&mut self) -> Option<&'a u32> {
        let key = self.inner.next()?;
        Some(key)
    }
}

impl ExactSizeIterator for Keys<'_> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl iter::FusedIterator for Keys<'_> {}

/// An owning iterator over the keys of a `DenseMap`.
///
/// This `struct` is created by the [`into_keys`] method on [`DenseMap`]. See its
/// documentation for more.
///
/// [`into_keys`]: DenseMap::into_keys
///
/// # Example
///
/// ```
/// use densemap::DenseMap;
///
/// let mut densemap = DenseMap::new();
/// densemap.insert(1);
/// let keys = densemap.into_keys();
/// ```
pub struct IntoKeys {
    inner: vec::IntoIter<u32>,
}

impl fmt::Debug for IntoKeys {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.inner.as_ref().iter()).finish()
    }
}

impl Iterator for IntoKeys {
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<u32> {
        let key = self.inner.next()?;
        Some(key)
    }
}

impl ExactSizeIterator for IntoKeys {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl iter::FusedIterator for IntoKeys {}

/// An iterator over the values of a `DenseMap`.
///
/// This `struct` is created by the [`values`] method on [`DenseMap`]. See its
/// documentation for more.
///
/// [`values`]: DenseMap::values
///
/// # Example
///
/// ```
/// use densemap::DenseMap;
///
/// let mut densemap = DenseMap::new();
/// densemap.insert(1);
/// let values = densemap.values();
/// ```
pub struct Values<'a, T> {
    inner: slice::Iter<'a, T>,
}

impl<T> Clone for Values<'_, T> {
    #[inline]
    fn clone(&self) -> Self {
        Values {
            inner: self.inner.clone(),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Values<'_, T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, T> Iterator for Values<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<&'a T> {
        let value = self.inner.next()?;
        Some(value)
    }
}

impl<T> ExactSizeIterator for Values<'_, T> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<T> iter::FusedIterator for Values<'_, T> {}

/// A mutable iterator over the value of a `DenseMap`.
///
/// This `struct` is created by the [`values_mut`] method on [`DenseMap`]. See its
/// documentation for more.
///
/// [`values_mut`]: DenseMap::values_mut
///
/// # Example
///
/// ```
/// use densemap::DenseMap;
///
/// let mut densemap = DenseMap::new();
/// densemap.insert(1);
/// let values = densemap.values_mut();
/// ```
pub struct ValuesMut<'a, T> {
    inner: slice::IterMut<'a, T>,
}

impl<T: fmt::Debug> fmt::Debug for ValuesMut<'_, T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.inner.as_ref().iter()).finish()
    }
}

impl<'a, T> Iterator for ValuesMut<'a, T> {
    type Item = &'a mut T;

    #[inline]
    fn next(&mut self) -> Option<&'a mut T> {
        let value = self.inner.next()?;
        Some(value)
    }
}

impl<T> ExactSizeIterator for ValuesMut<'_, T> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<T> iter::FusedIterator for ValuesMut<'_, T> {}

/// An owning iterator over the values of a `DenseMap`.
///
/// This `struct` is created by the [`into_values`] method on [`DenseMap`]. See its
/// documentation for more.
///
/// [`into_values`]: DenseMap::into_values
///
/// # Example
///
/// ```
/// use densemap::DenseMap;
///
/// let mut densemap = DenseMap::new();
/// densemap.insert(1);
/// let values = densemap.into_values();
/// ```
pub struct IntoValues<T> {
    inner: vec::IntoIter<T>,
}

impl<T: fmt::Debug> fmt::Debug for IntoValues<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.inner.as_ref().iter()).finish()
    }
}

impl<T> Iterator for IntoValues<T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        let value = self.inner.next()?;
        Some(value)
    }
}

impl<T> ExactSizeIterator for IntoValues<T> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<T> iter::FusedIterator for IntoValues<T> {}

/// An iterator over the entries of a `DenseMap`.
///
/// This `struct` is created by the [`iter`] method on [`DenseMap`]. See its
/// documentation for more.
///
/// [`iter`]: DenseMap::iter
///
/// # Example
///
/// ```
/// use densemap::DenseMap;
///
/// let mut densemap = DenseMap::new();
/// densemap.insert(1);
/// let iter = densemap.iter();
/// ```
pub struct Iter<'a, T> {
    inner_keys: slice::Iter<'a, u32>,
    inner_values: slice::Iter<'a, T>,
}

impl<T> Clone for Iter<'_, T> {
    #[inline]
    fn clone(&self) -> Self {
        Iter {
            inner_keys: self.inner_keys.clone(),
            inner_values: self.inner_values.clone(),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Iter<'_, T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (&'a u32, &'a T);

    #[inline]
    fn next(&mut self) -> Option<(&'a u32, &'a T)> {
        let key = self.inner_keys.next()?;
        let value = self.inner_values.next()?;
        Some((key, value))
    }
}

impl<T> ExactSizeIterator for Iter<'_, T> {
    #[inline]
    fn len(&self) -> usize {
        self.inner_keys.len()
    }
}

impl<T> iter::FusedIterator for Iter<'_, T> {}

/// A mutable iterator over the entries of a `DenseMap`.
///
/// This `struct` is created by the [`iter_mut`] method on [`DenseMap`]. See its
/// documentation for more.
///
/// [`iter_mut`]: DenseMap::iter_mut
///
/// # Example
///
/// ```
/// use densemap::DenseMap;
///
/// let mut densemap = DenseMap::new();
/// densemap.insert(1);
/// let iter = densemap.iter_mut();
/// ```
pub struct IterMut<'a, T> {
    inner_keys: slice::Iter<'a, u32>,
    inner_values: slice::IterMut<'a, T>,
}

impl<T: fmt::Debug> fmt::Debug for IterMut<'_, T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let keys = self.inner_keys.as_ref().iter();
        let values = self.inner_values.as_ref().iter();
        f.debug_list().entries(Iterator::zip(keys, values)).finish()
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = (&'a u32, &'a mut T);

    #[inline]
    fn next(&mut self) -> Option<(&'a u32, &'a mut T)> {
        let key = self.inner_keys.next()?;
        let value = self.inner_values.next()?;
        Some((key, value))
    }
}

impl<T> ExactSizeIterator for IterMut<'_, T> {
    #[inline]
    fn len(&self) -> usize {
        self.inner_keys.len()
    }
}

impl<T> iter::FusedIterator for IterMut<'_, T> {}

/// An iterator over the entries of a `DenseMap`, with mutable references to value.
///
/// This `struct` is created by the [`into_iter`] method on [`DenseMap`]. See its
/// documentation for more.
///
/// [`into_iter`]: DenseMap::into_iter
///
/// # Example
///
/// ```
/// use densemap::DenseMap;
///
/// let mut densemap = DenseMap::new();
/// densemap.insert(1);
/// let iter = densemap.into_iter();
/// ```
pub struct IntoIter<T> {
    inner_keys: vec::IntoIter<u32>,
    inner_values: vec::IntoIter<T>,
}

impl<T: fmt::Debug> fmt::Debug for IntoIter<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let keys = self.inner_keys.as_ref().iter();
        let values = self.inner_values.as_ref().iter();
        f.debug_list().entries(Iterator::zip(keys, values)).finish()
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = (u32, T);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let key = self.inner_keys.next()?;
        let value = self.inner_values.next()?;
        Some((key, value))
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {
    #[inline]
    fn len(&self) -> usize {
        self.inner_keys.len()
    }
}

impl<T> iter::FusedIterator for IntoIter<T> {}
