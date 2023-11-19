use ahash::{AHashMap, AHasher};
use datalog_syntax::AnonymousGroundAtom;
use std::collections::hash_map::Entry;
use std::hash::{Hash, Hasher};

#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Row(pub u64);

fn hashisher(key: &AnonymousGroundAtom) -> Row {
    let mut hasher = AHasher::default();

    key.iter()
        .for_each(|masked_value| masked_value.hash(&mut hasher));

    Row(hasher.finish())
}

#[derive(Default)]
pub struct FactRegistry {
    inner: AHashMap<Row, AnonymousGroundAtom>,
}

impl FactRegistry {
    pub fn register(&mut self, fact: AnonymousGroundAtom) -> Row {
        let hash = hashisher(&fact);

        return match self.inner.entry(hash) {
            Entry::Occupied(inner) => *inner.key(),
            Entry::Vacant(inner) => {
                let key = *inner.key();
                inner.insert(fact);

                key
            }
        };
    }
    pub fn compute_key(&self, fact: &AnonymousGroundAtom) -> Row {
        hashisher(fact)
    }
    pub fn get(&self, hash: Row) -> &AnonymousGroundAtom {
        return self.inner.get(&hash).unwrap();
    }
    pub fn contains(&self, fact: &AnonymousGroundAtom) -> bool {
        let key = self.compute_key(fact);

        self.inner.contains_key(&key)
    }
    pub fn remove(&mut self, hash: Row) -> AnonymousGroundAtom {
        self.inner.remove(&hash).unwrap()
    }
    pub fn insert_registered(&mut self, hash: Row, fact: AnonymousGroundAtom) {
        self.inner.insert(hash, fact);
    }
}
