use std::collections::{HashMap, HashSet};
use datalog_syntax::AnonymousGroundAtom;
use crate::helpers::program_transformations::DELTA_PREFIX;

pub type FactStorage = HashSet<AnonymousGroundAtom>;
#[derive(Default)]
pub struct RelationStorage {
    pub(crate) inner: HashMap<String, FactStorage>,
}

impl RelationStorage {
    pub(crate) fn get_relation(&self, relation: &str) -> Option<&HashSet<AnonymousGroundAtom>> {
        return self.inner.get(relation);
    }
    fn clear_delta_indexes(&mut self) {
        self
            .inner
            .keys()
            .clone()
            .for_each(|key| {
                if key.contains(DELTA_PREFIX) {
                    self.inner.remove(key);
                }
            });
    }

}
