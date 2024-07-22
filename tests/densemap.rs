use densemap::DenseMap;

#[test]
fn test_key() {
    let mut densemap = DenseMap::new();
    let key0 = densemap.insert(11);
    assert_eq!(key0, 0);

    let key1 = densemap.insert(11);
    assert_eq!(key1, 1);

    densemap.remove(key0);
    let key2 = densemap.insert(11);
    assert_eq!(key2, 0);
}

#[test]
fn test_pure() {
    let mut densemap0 = DenseMap::new();
    let mut densemap1 = DenseMap::new();

    let key00 = densemap0.insert(11);
    let key10 = densemap1.insert(32);
    assert_eq!(key00, key10);

    let key01 = densemap0.insert(11);
    let key11 = densemap1.insert(32);
    assert_eq!(key01, key11);

    densemap0.remove(key00);
    densemap1.remove(key10);
    let key02 = densemap0.insert(11);
    let key12 = densemap1.insert(32);
    assert_eq!(key02, key12);
}

#[test]
fn test_new() {
    let mut densemap = DenseMap::new();
    assert_eq!(densemap.capacity(), (0, 0));
    assert_eq!(densemap.len(), 0);

    densemap.insert(0);
    assert!(1 <= densemap.capacity().0);
    assert!(1 <= densemap.capacity().1);
    assert_eq!(densemap.len(), 1);
}

#[test]
fn test_with_capacity() {
    let mut densemap = DenseMap::with_capacity(30, 10);
    assert!(30 <= densemap.capacity().0);
    assert!(10 <= densemap.capacity().1);
    assert_eq!(densemap.len(), 0);

    densemap.insert(0);
    assert!(30 <= densemap.capacity().0);
    assert!(10 <= densemap.capacity().1);
    assert_eq!(densemap.len(), 1);
}

#[test]
fn test_reserve() {
    let mut densemap = DenseMap::<()>::new();
    assert_eq!(densemap.capacity(), (0, 0));

    densemap.reserve(40, 20);
    assert!(40 <= densemap.capacity().0);
    assert!(20 <= densemap.capacity().1);
}

#[test]
fn test_try_reserve() {
    let mut densemap = DenseMap::<()>::new();
    assert_eq!(densemap.capacity(), (0, 0));

    assert_eq!(densemap.try_reserve(15, 4), Ok(()));
    assert!(15 <= densemap.capacity().0);
    assert!(4 <= densemap.capacity().1);

    // should be error
    assert_ne!(densemap.try_reserve(isize::MAX as usize, 0), Ok(()));
    assert_ne!(densemap.try_reserve(0, isize::MAX as usize), Ok(()));
}

#[test]
fn test_shrink_to_fit() {
    let mut densemap = DenseMap::with_capacity(30, 10);
    assert!(30 <= densemap.capacity().0);
    assert!(10 <= densemap.capacity().1);

    densemap.insert(3);

    densemap.shrink_to_fit();
    assert!(1 <= densemap.capacity().0);
    assert!(1 <= densemap.capacity().1);
}

#[test]
fn test_shrink_to() {
    let mut densemap = DenseMap::<()>::with_capacity(200, 100);
    assert!(100 <= densemap.capacity().0);
    assert!(100 <= densemap.capacity().1);

    densemap.shrink_to(50, 25);
    assert!(50 <= densemap.capacity().0);
    assert!(25 <= densemap.capacity().1);
}

#[test]
fn test_len_and_is_empty() {
    let mut densemap = DenseMap::new();
    assert_eq!(densemap.len(), 0);
    assert!(densemap.is_empty());

    densemap.insert(12);
    assert_eq!(densemap.len(), 1);
    assert!(!densemap.is_empty());
}

#[test]
fn test_slice() {
    let mut densemap = DenseMap::new();
    let key0 = densemap.insert(32);
    let key1 = densemap.insert(64);
    let key2 = densemap.insert(128);
    assert_eq!(densemap.len(), 3);

    assert_eq!(densemap.as_key_slice(), &[key0, key1, key2]);
    assert_eq!(densemap.as_value_slice(), &[32, 64, 128]);

    densemap
        .as_value_mut_slice()
        .iter_mut()
        .for_each(|value| *value -= 1);
    assert_eq!(densemap.as_value_slice(), &[31, 63, 127]);
}

#[test]
fn test_iter() {
    let mut densemap = DenseMap::new();
    let key0 = densemap.insert(17);
    let key1 = densemap.insert(43);
    let key2 = densemap.insert(12);
    assert_eq!(densemap.len(), 3);

    let mut keys = densemap.keys();
    assert_eq!(keys.len(), 3);
    assert_eq!(keys.next(), Some(&key0));
    assert_eq!(keys.next(), Some(&key1));
    assert_eq!(keys.next(), Some(&key2));
    assert_eq!(keys.next(), None);

    let mut values = densemap.values();
    assert_eq!(values.len(), 3);
    assert_eq!(values.next(), Some(&17));
    assert_eq!(values.next(), Some(&43));
    assert_eq!(values.next(), Some(&12));
    assert_eq!(values.next(), None);

    let mut iter = densemap.iter();
    assert_eq!(iter.len(), 3);
    assert_eq!(iter.next(), Some((&key0, &17)));
    assert_eq!(iter.next(), Some((&key1, &43)));
    assert_eq!(iter.next(), Some((&key2, &12)));
    assert_eq!(iter.next(), None);
}

#[test]
fn test_iter_mut() {
    let mut densemap = DenseMap::new();
    let key0 = densemap.insert(6);
    let key1 = densemap.insert(96);
    let key2 = densemap.insert(0);
    assert_eq!(densemap.len(), 3);

    let values = densemap.values_mut();
    assert_eq!(values.len(), 3);
    values.for_each(|value| *value += 2);

    let mut values = densemap.values();
    assert_eq!(values.len(), 3);
    assert_eq!(values.next(), Some(&8));
    assert_eq!(values.next(), Some(&98));
    assert_eq!(values.next(), Some(&2));
    assert_eq!(values.next(), None);

    let iter = densemap.iter_mut();
    assert_eq!(iter.len(), 3);
    iter.for_each(|(_, value)| *value += 2);

    let mut iter = densemap.iter();
    assert_eq!(iter.len(), 3);
    assert_eq!(iter.next(), Some((&key0, &10)));
    assert_eq!(iter.next(), Some((&key1, &100)));
    assert_eq!(iter.next(), Some((&key2, &4)));
    assert_eq!(iter.next(), None);
}

#[test]
fn test_into_iter() {
    let mut densemap = DenseMap::new();
    let key0 = densemap.insert(24);
    let key1 = densemap.insert(63);
    let key2 = densemap.insert(3);
    assert_eq!(densemap.len(), 3);

    let mut keys = densemap.clone().into_keys();
    assert_eq!(keys.len(), 3);
    assert_eq!(keys.next(), Some(key0));
    assert_eq!(keys.next(), Some(key1));
    assert_eq!(keys.next(), Some(key2));
    assert_eq!(keys.next(), None);

    let mut values = densemap.clone().into_values();
    assert_eq!(values.len(), 3);
    assert_eq!(values.next(), Some(24));
    assert_eq!(values.next(), Some(63));
    assert_eq!(values.next(), Some(3));
    assert_eq!(values.next(), None);

    let mut iter = densemap.into_iter();
    assert_eq!(iter.len(), 3);
    assert_eq!(iter.next(), Some((key0, 24)));
    assert_eq!(iter.next(), Some((key1, 63)));
    assert_eq!(iter.next(), Some((key2, 3)));
    assert_eq!(iter.next(), None);
}

#[test]
fn test_for() {
    let mut densemap = DenseMap::new();
    let key0 = densemap.insert(106);
    let key1 = densemap.insert(17);
    let key2 = densemap.insert(82);

    for (&key, &value) in &densemap {
        match key {
            _ if key == key0 => assert_eq!(value, 106),
            _ if key == key1 => assert_eq!(value, 17),
            _ if key == key2 => assert_eq!(value, 82),
            _ => unreachable!(),
        }
    }

    for (_, value) in &mut densemap {
        *value += 2;
    }

    for (key, value) in densemap {
        match key {
            _ if key == key0 => assert_eq!(value, 108),
            _ if key == key1 => assert_eq!(value, 19),
            _ if key == key2 => assert_eq!(value, 84),
            _ => unreachable!(),
        }
    }
}

#[test]
fn test_iter_clone() {
    let mut densemap = DenseMap::new();
    densemap.insert(106);
    densemap.insert(17);
    densemap.insert(82);

    let keys = densemap.keys();
    let equality = Iterator::zip(keys.clone(), keys).all(|(key0, key1)| key0 == key1);
    assert!(equality);

    let values = densemap.values();
    let equality = Iterator::zip(values.clone(), values).all(|(value0, value1)| value0 == value1);
    assert!(equality);

    let iter = densemap.iter();
    let equality = Iterator::zip(iter.clone(), iter).all(|(entry0, entry1)| entry0 == entry1);
    assert!(equality);
}

#[test]
fn test_drain() {
    let mut densemap = DenseMap::new();
    let key0 = densemap.insert(106);
    let key1 = densemap.insert(17);
    let key2 = densemap.insert(82);
    assert!(3 <= densemap.capacity().0);
    assert!(3 <= densemap.capacity().1);
    assert_eq!(densemap.len(), 3);

    let mut drain = densemap.drain();
    assert_eq!(drain.len(), 3);
    assert_eq!(drain.next(), Some((key0, 106)));
    assert_eq!(drain.next(), Some((key1, 17)));
    assert_eq!(drain.next(), Some((key2, 82)));
    assert_eq!(drain.next(), None);
    drop(drain);

    assert!(3 <= densemap.capacity().0);
    assert!(3 <= densemap.capacity().1);
    assert_eq!(densemap.len(), 0);
}

#[test]
fn test_clear() {
    let mut densemap = DenseMap::from([12, 213, 4, 23, 34, 543]);
    assert!(6 <= densemap.capacity().0);
    assert!(6 <= densemap.capacity().1);
    assert_eq!(densemap.len(), 6);

    densemap.clear();

    assert!(6 <= densemap.capacity().0);
    assert!(6 <= densemap.capacity().1);
    assert_eq!(densemap.len(), 0);
}

#[test]
fn test_contain_key_and_get() {
    let mut densemap = DenseMap::new();
    let key = densemap.insert(7);

    // exists value
    assert!(densemap.contain_key(key));
    assert_eq!(densemap.get(key), Some(&7));
    assert_eq!(densemap.get_key_value(key), Some((&key, &7)));

    // change value
    densemap.get_mut(key).map(|value| *value += 14);
    assert!(densemap.contain_key(key));
    assert_eq!(densemap.get(key), Some(&21));
    assert_eq!(densemap.get_key_value(key), Some((&key, &21)));

    // no exists value
    densemap.remove(key);
    assert!(!densemap.contain_key(key));
    assert_eq!(densemap.get(key), None);
    assert_eq!(densemap.get_key_value(key), None);
    assert_eq!(densemap.get_mut(key), None);

    // no match key version
    let new_key = densemap.insert(59);
    // assert!(!densemap.contain_key(key));
    // assert_eq!(densemap.get(key), None);
    // assert_eq!(densemap.get_key_value(key), None);
    // assert_eq!(densemap.get_mut(key), None);

    // with swapped value
    densemap.insert(58);
    densemap.remove(new_key);
    assert!(!densemap.contain_key(key));
    assert_eq!(densemap.get(key), None);
    assert_eq!(densemap.get_key_value(key), None);
    assert_eq!(densemap.get_mut(key), None);
}

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
fn test_insert_and_remove() {
    let mut densemap = DenseMap::new();
    let key = densemap.insert(0);
    densemap.remove(key);

    let new_key = densemap.insert(1);
    // assert_eq!(densemap.get(key), None);
    assert_eq!(densemap.get(new_key), Some(&1));

    // assert_eq!(densemap.remove(key), None);
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
fn test_insert_and_remove_multiple() {
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
    assert_eq!(densemap.get(new_key0), Some(&3));
    assert_eq!(densemap.get(new_key1), Some(&4));
    assert_eq!(densemap.get(new_key2), Some(&5));

    assert_eq!(densemap.remove(new_key0), Some(3));
    assert_eq!(densemap.remove(new_key1), Some(4));
    assert_eq!(densemap.remove(new_key2), Some(5));
    assert_eq!(densemap.remove(new_key0), None);
    assert_eq!(densemap.remove(new_key1), None);
    assert_eq!(densemap.remove(new_key2), None);
}

#[test]
fn test_equal() {
    let mut densemap0 = DenseMap::new();
    densemap0.insert(0);
    densemap0.insert(1);
    densemap0.insert(2);

    let mut densemap1 = DenseMap::new();
    densemap1.insert(0);
    densemap1.insert(1);
    densemap1.insert(2);

    assert_eq!(densemap0, densemap1);

    // empty
    assert_eq!(DenseMap::<()>::new(), DenseMap::<()>::new());

    // should be false
    // different values
    densemap0.iter_mut().for_each(|(_, value)| *value += 1);
    assert_ne!(densemap0, densemap1);

    // should be false
    // different len
    let mut densemap0 = DenseMap::new();
    densemap0.insert(0);
    assert_ne!(densemap0, densemap1);
}

#[test]
fn test_default() {
    assert_eq!(DenseMap::<()>::default(), DenseMap::<()>::new());
}

#[test]
fn test_index() {
    let mut densemap = DenseMap::new();
    let key0 = densemap.insert(0);
    let key1 = densemap.insert(1);
    let key2 = densemap.insert(2);

    assert_eq!(densemap[key0], 0);
    assert_eq!(densemap[key1], 1);
    assert_eq!(densemap[key2], 2);
    assert_eq!(densemap.len(), 3);

    densemap[key1] = 123;

    assert_eq!(densemap[key0], 0);
    assert_eq!(densemap[key1], 123);
    assert_eq!(densemap[key2], 2);
    assert_eq!(densemap.len(), 3);
}
