use ahash::{AHasher, HashMap};
use datalog_syntax::AnonymousGroundAtom;
use std::collections::hash_map::Entry;
use std::hash::{Hash, Hasher};

fn hashisher(key: &AnonymousGroundAtom) -> usize {
    let mut hasher = AHasher::default();

    key.iter()
        .for_each(|masked_value| masked_value.hash(&mut hasher));

    hasher.finish() as usize
}

#[derive(Default)]
pub struct FactRegistry {
    inner: HashMap<usize, AnonymousGroundAtom>,
}

impl FactRegistry {
    pub fn register(&mut self, fact: AnonymousGroundAtom) -> usize {
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
    pub fn compute_key(&self, fact: &AnonymousGroundAtom) -> usize {
        hashisher(fact)
    }
    pub fn get(&self, hash: usize) -> &AnonymousGroundAtom {
        return self.inner.get(&hash).unwrap();
    }
    pub fn contains(&self, fact: &AnonymousGroundAtom) -> bool {
        let key = self.compute_key(fact);

        self.inner.contains_key(&key)
    }
}
