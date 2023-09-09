use crate::engine::storage::RelationStorage;
use datalog_syntax::*;
use crate::evaluation::query::pattern_match;
use crate::evaluation::semi_naive::semi_naive_evaluation;
use crate::helpers::helpers::DELTA_PREFIX;

pub struct ChibiRuntime {
    processed: RelationStorage,
    unprocessed_insertions: RelationStorage,
    unprocessed_deletions: RelationStorage,
    program: Program,
}

impl ChibiRuntime {
    pub fn insert(&mut self, relation: &str, ground_atom: AnonymousGroundAtom) -> bool {
        self.unprocessed_insertions.insert(relation, ground_atom)
    }
    /*fn remove(&mut self, query: &Query) -> impl Iterator<Item=AnonymousGroundAtom> {
        let matches: Vec<_> = self
            .processed
            .inner
            .get(query.symbol)
            .unwrap()
            .iter()
            .filter(|fact| {
                pattern_match(query, fact)
            })
            .collect();
    }*/
    pub fn contains(&self, relation: &str, ground_atom: &AnonymousGroundAtom) -> bool {
        if !self.processed.contains(relation, ground_atom) {
            return self.unprocessed_insertions.contains(relation, ground_atom)
        }

        true
    }
    fn query<'a>(&'a self, query: &'a Query) -> impl Iterator<Item=&AnonymousGroundAtom> + '_ {
        self
            .processed
            .inner
            .get(query.symbol)
            .unwrap()
            .iter()
            .filter(|fact| {
                pattern_match(query, fact)
            })
    }
    pub fn poll(&mut self) {
        self
            .unprocessed_insertions
            .drain_all_relations()
            .for_each(|(relation_symbol, unprocessed_facts)| {
                // We dump all unprocessed EDB relations into delta EDB relations
                self
                    .processed
                    // This clone hurts.
                    .insert_all(&format!("{}{}", DELTA_PREFIX, relation_symbol), unprocessed_facts.clone().into_iter());
                // And in their respective place
                self
                    .processed
                    .insert_all(relation_symbol, unprocessed_facts.into_iter())
            });

        semi_naive_evaluation(&mut self.processed, &self.program, true);
    }
    pub fn new(program: Program) -> Self {
        let processed = Default::default();
        let unprocessed_insertions = Default::default();
        let unprocessed_deletions = Default::default();

        Self {
            processed,
            unprocessed_insertions,
            unprocessed_deletions,
            program,
        }
    }
    pub fn safe(&self) -> bool {
        self.unprocessed_insertions.len() == 0
    }
}