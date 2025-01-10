use std::collections::{BTreeMap, HashMap};
use std::hash::Hash;
use std::option::Option;

/// A set which tracks the occurrence count of each element, defaulting to 0 for elements which have
/// never been inserted.
pub struct BTreeMultiSet<T> {
  occurrence_count: BTreeMap<T, usize>,
}

impl<T: Ord> BTreeMultiSet<T> {
  /// Creates a new multiset where all elements have occurrence count 0.
  pub fn new() -> Self {
    BTreeMultiSet {
      occurrence_count: BTreeMap::new(),
    }
  }

  /// The difference between the number of insertions and the number of successful removals of the
  /// given element. Elements which have never been encountered will have an occurrence count of 0.
  pub fn get_count(&self, element: &T) -> usize {
    *self.occurrence_count.get(element).unwrap_or(&0)
  }

  /// Increments the occurence count of the element by the given amount and returns the updated
  /// count. If this is the first time the element has been inserted and the intended count is
  /// positive, it will be cloned for internal tracking.
  pub fn insert(&mut self, element: &T, n: usize) -> usize
  where
    T: Clone,
  {
    if let Some(count) = self.occurrence_count.get_mut(element) {
      *count += n;
      *count
    } else {
      if n != 0 {
        self.occurrence_count.insert(element.clone(), n);
      }
      n
    }
  }

  /// If the occurrence count of `element` is greater than or equal to `n`, reduces it by `n` and
  /// returns the updated count. Otherwise, does nothing and returns None.
  pub fn remove(&mut self, element: &T, n: usize) -> Option<usize> {
    if n == 0 {
      return Some(self.get_count(element));
    }

    let mut updated_count: Option<usize> = None;
    if let Some(count) = self.occurrence_count.get_mut(element) {
      if *count >= n {
        *count -= n;
        updated_count = Some(*count);

        if *count == 0 {
          self.occurrence_count.remove(element);
        }
      }
    }
    updated_count
  }

  /// Resets the occurrence count of all elements to 0.
  pub fn clear(&mut self) {
    self.occurrence_count.clear()
  }

  // Returns the number of elements with positive occurrence counts.
  pub fn len(&self) -> usize {
    self.occurrence_count.len()
  }

  // An iterator visiting all (element, occurrence_count) pairs in ascending key order.
  pub fn iter<'a>(&'a self) -> impl Iterator<Item = (&T, usize)> + 'a {
    BTreeMultiSetIter {
      delegate: self.occurrence_count.iter(),
    }
  }
}

struct BTreeMultiSetIter<'a, T> {
  delegate: std::collections::btree_map::Iter<'a, T, usize>,
}

impl<'a, T> Iterator for BTreeMultiSetIter<'a, T> {
  type Item = (&'a T, usize);

  fn next(&mut self) -> Option<Self::Item> {
    self.delegate.next().map(|(element, count)| (element, *count))
  }
}

/// A set which tracks the occurrence count of each element, defaulting to 0 for elements which have
/// never been inserted.
pub struct HashMultiSet<T> {
  occurrence_count: HashMap<T, usize>,
}

impl<T: Hash + Eq> HashMultiSet<T> {
  /// Creates a new multiset where all elements have occurrence count 0.
  pub fn new() -> Self {
    HashMultiSet {
      occurrence_count: HashMap::new(),
    }
  }

  /// The difference between the number of insertions and the number of successful removals of the
  /// given element. Elements which have never been encountered will have an occurrence count of 0.
  pub fn get_count(&self, element: &T) -> usize {
    *self.occurrence_count.get(element).unwrap_or(&0)
  }

  /// Increments the occurence count of the element by the given amount and returns the updated
  /// count. If this is the first time the element has been inserted and the intended count is
  /// positive, it will be cloned for internal tracking.
  pub fn insert(&mut self, element: &T, n: usize) -> usize
  where
    T: Clone,
  {
    if let Some(count) = self.occurrence_count.get_mut(element) {
      *count += n;
      *count
    } else {
      if n != 0 {
        self.occurrence_count.insert(element.clone(), n);
      }
      n
    }
  }

  /// If the occurrence count of `element` is greater than or equal to `n`, reduces it by `n` and
  /// returns the updated count. Otherwise, does nothing and returns None.
  pub fn remove(&mut self, element: &T, n: usize) -> Option<usize> {
    if n == 0 {
      return Some(self.get_count(element));
    }

    let mut updated_count: Option<usize> = None;
    if let Some(count) = self.occurrence_count.get_mut(element) {
      if *count >= n {
        *count -= n;
        updated_count = Some(*count);

        if *count == 0 {
          self.occurrence_count.remove(element);
        }
      }
    }
    updated_count
  }

  /// Resets the occurrence count of all elements to 0.
  pub fn clear(&mut self) {
    self.occurrence_count.clear()
  }

  // Returns the number of elements with positive occurrence counts.
  pub fn len(&self) -> usize {
    self.occurrence_count.len()
  }

  // An iterator visiting all (element, occurrence_count) pairs.
  pub fn iter<'a>(&'a self) -> impl Iterator<Item = (&T, usize)> + 'a {
    HashMultiSetIter {
      delegate: self.occurrence_count.iter(),
    }
  }
}

struct HashMultiSetIter<'a, T> {
  delegate: std::collections::hash_map::Iter<'a, T, usize>,
}

impl<'a, T> Iterator for HashMultiSetIter<'a, T> {
  type Item = (&'a T, usize);

  fn next(&mut self) -> Option<Self::Item> {
    self.delegate.next().map(|(element, count)| (element, *count))
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn btreemultiset_empty_len_zero() {
    let multiset = BTreeMultiSet::<String>::new();

    assert_eq!(multiset.len(), 0);
  }

  #[test]
  fn btreemultiset_empty_count_zero() {
    let multiset = BTreeMultiSet::<String>::new();

    assert_eq!(multiset.get_count(&String::from("test")), 0);
  }

  #[test]
  fn btreemultiset_empty_remove_zero_succeeds() {
    let mut multiset = BTreeMultiSet::<String>::new();

    assert_eq!(multiset.remove(&String::from("test"), 0), Some(0));
  }

  #[test]
  fn btreemultiset_empty_remove_one_fails() {
    let mut multiset = BTreeMultiSet::<String>::new();

    assert_eq!(multiset.remove(&String::from("test"), 1), None);
  }

  #[test]
  fn btreemultiset_insert_zero_noop() {
    let mut multiset = BTreeMultiSet::<String>::new();

    multiset.insert(&String::from("test"), 0);
    assert_eq!(multiset.len(), 0);
  }

  #[test]
  fn btreemultiset_insert_adds_count() {
    let mut multiset = BTreeMultiSet::<String>::new();
    let key = String::from("test");

    assert_eq!(multiset.insert(&key, 3), 3);
    assert_eq!(multiset.get_count(&key), 3);

    assert_eq!(multiset.insert(&key, 4), 7);
    assert_eq!(multiset.get_count(&key), 7);
  }

  #[test]
  fn btreemultiset_len_counts_nonzero_elements() {
    let mut multiset = BTreeMultiSet::<String>::new();

    multiset.insert(&String::from("test1"), 1);
    multiset.insert(&String::from("test2"), 2);

    assert_eq!(multiset.len(), 2);
  }

  #[test]
  fn btreemultiset_len_unchanged_after_element_update() {
    let mut multiset = BTreeMultiSet::<String>::new();
    let key = String::from("test");

    multiset.insert(&key, 1);
    multiset.insert(&key, 2);

    assert_eq!(multiset.len(), 1);
  }

  #[test]
  fn btreemultiset_insert_remove_success() {
    let mut multiset = BTreeMultiSet::<String>::new();
    let key = String::from("test");

    multiset.insert(&key, 10);

    assert_eq!(multiset.remove(&key, 9), Some(1));
    assert_eq!(multiset.get_count(&key), 1);
  }

  #[test]
  fn btreemultiset_len_decreases_after_full_removal() {
    let mut multiset = BTreeMultiSet::<String>::new();
    let key = String::from("test");

    multiset.insert(&key, 10);

    multiset.remove(&key, 9);
    assert_eq!(multiset.len(), 1);

    multiset.remove(&key, 1);
    assert_eq!(multiset.len(), 0);
  }

  #[test]
  fn btreemultiset_insert_remove_fail() {
    let mut multiset = BTreeMultiSet::<String>::new();
    let key = String::from("test");

    multiset.insert(&key, 10);

    assert_eq!(multiset.remove(&key, 11), None);
    assert_eq!(multiset.get_count(&key), 10);
  }

  #[test]
  fn btreemultiset_multiple_keys_updated_independently() {
    let mut multiset = BTreeMultiSet::<String>::new();
    let key1 = String::from("test1");
    let key2 = String::from("test2");

    assert_eq!(multiset.insert(&key1, 10), 10);
    assert_eq!(multiset.insert(&key2, 19), 19);

    assert_eq!(multiset.insert(&key1, 15), 25);
    assert_eq!(multiset.remove(&key2, 3), Some(16));

    assert_eq!(multiset.get_count(&key1), 25);
    assert_eq!(multiset.get_count(&key2), 16);
  }

  #[test]
  fn btreemultiset_clear() {
    let mut multiset = BTreeMultiSet::<String>::new();
    let key1 = String::from("def");
    let key2 = String::from("abc");

    multiset.insert(&key1, 7);
    multiset.insert(&key2, 12);
    multiset.clear();

    assert_eq!(multiset.get_count(&key1), 0);
    assert_eq!(multiset.get_count(&key2), 0);
    assert_eq!(multiset.len(), 0);
  }

  #[test]
  fn btreemultiset_iter_returns_occurrence_count_pairs_asc_order() {
    let mut multiset = BTreeMultiSet::<String>::new();
    let key1 = String::from("def");
    let key2 = String::from("abc");

    multiset.insert(&key1, 7);
    multiset.insert(&key2, 12);

    let counts: Vec<(&String, usize)> = multiset.iter().collect();
    assert_eq!(counts, Vec::from([(&key2, 12), (&key1, 7)]));
  }

  #[test]
  fn hashmultiset_empty_len_zero() {
    let multiset = HashMultiSet::<String>::new();

    assert_eq!(multiset.len(), 0);
  }

  #[test]
  fn hashmultiset_empty_count_zero() {
    let multiset = HashMultiSet::<String>::new();

    assert_eq!(multiset.get_count(&String::from("test")), 0);
  }

  #[test]
  fn hashmultiset_empty_remove_zero_succeeds() {
    let mut multiset = HashMultiSet::<String>::new();

    assert_eq!(multiset.remove(&String::from("test"), 0), Some(0));
  }

  #[test]
  fn hashmultiset_empty_remove_one_fails() {
    let mut multiset = HashMultiSet::<String>::new();

    assert_eq!(multiset.remove(&String::from("test"), 1), None);
  }

  #[test]
  fn hashmultiset_insert_zero_noop() {
    let mut multiset = HashMultiSet::<String>::new();

    multiset.insert(&String::from("test"), 0);
    assert_eq!(multiset.len(), 0);
  }

  #[test]
  fn hashmultiset_insert_adds_count() {
    let mut multiset = HashMultiSet::<String>::new();
    let key = String::from("test");

    assert_eq!(multiset.insert(&key, 3), 3);
    assert_eq!(multiset.get_count(&key), 3);

    assert_eq!(multiset.insert(&key, 4), 7);
    assert_eq!(multiset.get_count(&key), 7);
  }

  #[test]
  fn hashmultiset_len_counts_nonzero_elements() {
    let mut multiset = HashMultiSet::<String>::new();

    multiset.insert(&String::from("test1"), 1);
    multiset.insert(&String::from("test2"), 2);

    assert_eq!(multiset.len(), 2);
  }

  #[test]
  fn hashmultiset_len_unchanged_after_element_update() {
    let mut multiset = HashMultiSet::<String>::new();
    let key = String::from("test");

    multiset.insert(&key, 1);
    multiset.insert(&key, 2);

    assert_eq!(multiset.len(), 1);
  }

  #[test]
  fn hashmultiset_insert_remove_success() {
    let mut multiset = HashMultiSet::<String>::new();
    let key = String::from("test");

    multiset.insert(&key, 10);

    assert_eq!(multiset.remove(&key, 9), Some(1));
    assert_eq!(multiset.get_count(&key), 1);
  }

  #[test]
  fn hashmultiset_len_decreases_after_full_removal() {
    let mut multiset = HashMultiSet::<String>::new();
    let key = String::from("test");

    multiset.insert(&key, 10);

    multiset.remove(&key, 9);
    assert_eq!(multiset.len(), 1);

    multiset.remove(&key, 1);
    assert_eq!(multiset.len(), 0);
  }

  #[test]
  fn hashmultiset_insert_remove_fail() {
    let mut multiset = HashMultiSet::<String>::new();
    let key = String::from("test");

    multiset.insert(&key, 10);

    assert_eq!(multiset.remove(&key, 11), None);
    assert_eq!(multiset.get_count(&key), 10);
  }

  #[test]
  fn hashmultiset_multiple_keys_updated_independently() {
    let mut multiset = HashMultiSet::<String>::new();
    let key1 = String::from("test1");
    let key2 = String::from("test2");

    assert_eq!(multiset.insert(&key1, 10), 10);
    assert_eq!(multiset.insert(&key2, 19), 19);

    assert_eq!(multiset.insert(&key1, 15), 25);
    assert_eq!(multiset.remove(&key2, 3), Some(16));

    assert_eq!(multiset.get_count(&key1), 25);
    assert_eq!(multiset.get_count(&key2), 16);
  }

  #[test]
  fn hashmultiset_clear() {
    let mut multiset = HashMultiSet::<String>::new();
    let key1 = String::from("def");
    let key2 = String::from("abc");

    multiset.insert(&key1, 7);
    multiset.insert(&key2, 12);
    multiset.clear();

    assert_eq!(multiset.get_count(&key1), 0);
    assert_eq!(multiset.get_count(&key2), 0);
    assert_eq!(multiset.len(), 0);
  }

  #[test]
  fn hashmultiset_iter_returns_occurrence_count_pairs_asc_order() {
    let mut multiset = HashMultiSet::<String>::new();
    let key1 = String::from("def");
    let key2 = String::from("abc");

    multiset.insert(&key1, 7);
    multiset.insert(&key2, 12);

    let counts: Vec<(&String, usize)> = multiset.iter().collect();
    assert!(counts.contains(&(&key1, 7)));
    assert!(counts.contains(&(&key2, 12)));
  }
}
