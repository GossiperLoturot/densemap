/// A key of dense map, represents a position within dense map.
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
#[derive(Default, Clone, Copy, PartialEq, Eq, Debug)]
pub struct Key {
    idx: u32,
    generation: u32,
}

// A sparse index entry
#[derive(Clone, Debug)]
struct Entry {
    // even number is occupied, odd number is vacant.
    generation: u32,
    // A position when occupied, a next free position when vacant.
    idx_or_next: u32,
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
#[derive(Default, Clone, Debug)]
pub struct DenseMap<T> {
    next: u32,
    entries: Vec<Entry>,
    keys: Vec<Key>,
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
    pub fn new() -> Self {
        Self::with_capacity(0)
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
    /// let densemap: DenseMap<i32> = DenseMap::with_capacity(10);
    /// assert_eq!(densemap.len(), 0);
    /// assert!(10 <= densemap.capacity());
    /// ```
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            next: 0,
            entries: Vec::with_capacity(capacity),
            keys: Vec::with_capacity(capacity),
            values: Vec::with_capacity(capacity),
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
    /// let mut densemap = DenseMap::with_capacity(10);
    /// densemap.insert(42);
    /// assert!(10 <= densemap.capacity());
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        self.values.capacity()
    }

    /// Returns `true` if the dense map contains elements at that position
    /// within the dense map.
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
    pub fn contain_key(&self, key: Key) -> bool {
        if key.generation & 1 != 0 {
            return false;
        }

        if let Some(entry) = self.entries.get(key.idx as usize) {
            if key.generation == entry.generation {
                return true;
            }
        }

        false
    }

    /// Appends an element to the back of collection and
    /// returns stable unique key.
    ///
    /// Note that this method is a performance of *O*(*1*).
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
    /// let mut densemap = DenseMap::new();
    /// let key = densemap.insert(3);
    /// assert_eq!(densemap.get(key), Some(&3));
    /// ```
    pub fn insert(&mut self, value: T) -> Key {
        if self.next < self.entries.len() as u32 {
            let entry = self.entries.get_mut(self.next as usize).unwrap();
            let key = Key {
                idx: self.next,
                generation: entry.generation + 1,
            };
            self.next = entry.idx_or_next;
            entry.generation += 1;
            entry.idx_or_next = self.values.len() as u32;
            self.keys.push(key);
            self.values.push(value);
            key
        } else {
            let entry = Entry {
                generation: 0,
                idx_or_next: self.values.len() as u32,
            };
            let key = Key {
                idx: self.entries.len() as u32,
                generation: 0,
            };
            // self.next += 1;
            self.entries.push(entry);
            self.keys.push(key);
            self.values.push(value);
            self.next += 1;
            key
        }
    }

    /// Removes and returns the element at that position or `None` if out of bounds.
    ///
    /// Note that this method is a performance of *O*(*1*).
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
    pub fn remove(&mut self, key: Key) -> Option<T> {
        if key.generation & 1 != 0 {
            return None;
        }

        if let Some(entry) = self.entries.get_mut(key.idx as usize) {
            if entry.generation == key.generation {
                let idx = entry.idx_or_next;
                entry.generation += 1;
                entry.idx_or_next = self.next;
                self.next = key.idx;
                let _key = self.keys.swap_remove(idx as usize);
                let value = self.values.swap_remove(idx as usize);
                if idx < self.values.len() as u32 {
                    self.entries[self.keys[idx as usize].idx as usize].idx_or_next = idx;
                }
                return Some(value);
            }
        }

        None
    }

    /// Returns a reference to the value at that position or `None` if out of bounds.
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
    pub fn get(&self, key: Key) -> Option<&T> {
        if key.generation & 1 != 0 {
            return None;
        }

        if let Some(entry) = self.entries.get(key.idx as usize) {
            if key.generation == entry.generation {
                let value = self.values.get(entry.idx_or_next as usize).unwrap();
                return Some(value);
            }
        }

        None
    }

    /// Returns a mutable reference to the value at that position or `None` if out of bounds.
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
    pub fn get_mut(&mut self, key: Key) -> Option<&mut T> {
        if key.generation & 1 != 0 {
            return None;
        }

        if let Some(entry) = self.entries.get(key.idx as usize) {
            if key.generation == entry.generation {
                let value = self.values.get_mut(entry.idx_or_next as usize).unwrap();
                return Some(value);
            }
        }

        None
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
        self.next = 0;
        self.entries.clear();
        self.keys.clear();
        self.values.clear();
    }

    /// Returns the number of elements in the dense map, also referred to
    /// as its 'length'.
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
        self.values.len()
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
        self.values.is_empty()
    }

    /// Returns an iterator that is, one that moves each value out of
    /// the dense map (from start to end).
    ///
    /// Note: Because using contiguous array, it is
    /// same performance with slice iterator.
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
    ///
    /// assert_eq!(iter.next(), Some(&12));
    /// assert_eq!(iter.next(), Some(&34));
    /// assert_eq!(iter.next(), None);
    /// ```
    #[inline]
    pub fn iter(&self) -> std::slice::Iter<T> {
        self.values.iter()
    }

    /// Returns an iterator that is, one that moves each value out of
    /// the dense map (from start to end), and allow modifying each value.
    ///
    /// Note: Because using contiguous array, it is
    /// same performance with slice iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use densemap::DenseMap;
    ///
    /// let mut densemap = DenseMap::new();
    /// densemap.insert(12);
    /// densemap.insert(34);
    ///
    /// for value in densemap.iter_mut() {
    ///     *value += 2;
    /// }
    ///
    /// let mut iter = densemap.iter();
    /// assert_eq!(iter.next(), Some(&14));
    /// assert_eq!(iter.next(), Some(&36));
    /// assert_eq!(iter.next(), None);
    /// ```
    #[inline]
    pub fn iter_mut(&mut self) -> std::slice::IterMut<T> {
        self.values.iter_mut()
    }
}

#[cfg(test)]
mod test {
    use super::DenseMap;

    #[test]
    fn test_insert() {
        let mut densemap = DenseMap::new();
        let key = densemap.insert(0);
        assert_eq!(densemap.get(key), Some(&0));
    }

    #[test]
    fn test_remove() {
        let mut densemap = DenseMap::new();
        let key = densemap.insert(0);
        assert_eq!(densemap.remove(key), Some(0));
        assert_eq!(densemap.get(key), None);
        assert_eq!(densemap.remove(key), None);
    }

    #[test]
    fn test_insert_remove() {
        let mut densemap = DenseMap::new();
        let key = densemap.insert(0);
        densemap.remove(key);

        let new_key = densemap.insert(1);
        assert_eq!(densemap.get(key), None);
        assert_eq!(densemap.get(new_key), Some(&1));

        assert_eq!(densemap.remove(key), None);
        assert_eq!(densemap.remove(new_key), Some(1));
        assert_eq!(densemap.remove(new_key), None);
    }

    #[test]
    fn test_insert_multiple() {
        let mut densemap = DenseMap::new();
        let key0 = densemap.insert(0);
        let key1 = densemap.insert(1);
        let key2 = densemap.insert(2);
        assert_eq!(densemap.get(key0), Some(&0));
        assert_eq!(densemap.get(key1), Some(&1));
        assert_eq!(densemap.get(key2), Some(&2));
    }

    #[test]
    fn test_remove_multiple() {
        let mut densemap = DenseMap::new();
        let key0 = densemap.insert(0);
        let key1 = densemap.insert(1);
        let key2 = densemap.insert(2);
        assert_eq!(densemap.remove(key0), Some(0));
        assert_eq!(densemap.remove(key1), Some(1));
        assert_eq!(densemap.remove(key2), Some(2));
        assert_eq!(densemap.get(key0), None);
        assert_eq!(densemap.get(key1), None);
        assert_eq!(densemap.get(key2), None);
        assert_eq!(densemap.remove(key0), None);
        assert_eq!(densemap.remove(key1), None);
        assert_eq!(densemap.remove(key2), None);
    }

    #[test]
    fn test_insert_remove_multiple() {
        let mut densemap = DenseMap::new();
        let key0 = densemap.insert(0);
        let key1 = densemap.insert(1);
        let key2 = densemap.insert(2);
        densemap.remove(key0);
        densemap.remove(key1);
        densemap.remove(key2);

        let new_key0 = densemap.insert(3);
        let new_key1 = densemap.insert(4);
        let new_key2 = densemap.insert(5);
        assert_eq!(densemap.get(key0), None);
        assert_eq!(densemap.get(key1), None);
        assert_eq!(densemap.get(key2), None);
        assert_eq!(densemap.get(new_key0), Some(&3));
        assert_eq!(densemap.get(new_key1), Some(&4));
        assert_eq!(densemap.get(new_key2), Some(&5));

        assert_eq!(densemap.remove(key0), None);
        assert_eq!(densemap.remove(key1), None);
        assert_eq!(densemap.remove(key2), None);
        assert_eq!(densemap.remove(new_key0), Some(3));
        assert_eq!(densemap.remove(new_key1), Some(4));
        assert_eq!(densemap.remove(new_key2), Some(5));
        assert_eq!(densemap.remove(new_key0), None);
        assert_eq!(densemap.remove(new_key1), None);
        assert_eq!(densemap.remove(new_key2), None);
    }
}
