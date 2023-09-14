use crate::engine::storage::RelationStorage;
use crate::evaluation::query::pattern_match;
use crate::evaluation::semi_naive::semi_naive_evaluation;
use crate::helpers::helpers::{split_program, DELTA_PREFIX};
use crate::program_transformations::delta_program::make_delta_program;
use datalog_syntax::*;
use std::collections::HashSet;

pub struct ChibiRuntime {
    processed: RelationStorage,
    unprocessed_insertions: RelationStorage,
    unprocessed_deletions: RelationStorage,
    program: Program,
    nonrecursive_program: Program,
    recursive_program: Program,
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
    pub fn contains(
        &self,
        relation: &str,
        ground_atom: &AnonymousGroundAtom,
    ) -> Result<bool, String> {
        if !self.safe() {
            return Err("poll needed to obtain correct results".to_string());
        }

        if !self.processed.contains(relation, ground_atom) {
            return Ok(self.unprocessed_insertions.contains(relation, ground_atom));
        }

        Ok(true)
    }
    fn query<'a>(
        &'a self,
        query: &'a Query,
    ) -> Result<impl Iterator<Item = &AnonymousGroundAtom>, String> {
        if !self.safe() {
            return Err("poll needed to obtain correct results".to_string());
        }

        Ok(self
            .processed
            .inner
            .get(query.symbol)
            .unwrap()
            .iter()
            .filter(|fact| pattern_match(query, fact)))
    }
    pub fn poll(&mut self) {
        self.unprocessed_insertions.drain_all_relations().for_each(
            |(relation_symbol, unprocessed_facts)| {
                // We dump all unprocessed EDB relations into delta EDB relations
                self.processed
                    // This clone hurts.
                    .insert_all(
                        &format!("{}{}", DELTA_PREFIX, relation_symbol),
                        unprocessed_facts.clone().into_iter(),
                    );
                // And in their respective place
                self.processed
                    .insert_all(relation_symbol, unprocessed_facts.into_iter())
            },
        );

        semi_naive_evaluation(
            &mut self.processed,
            &self.nonrecursive_program,
            &self.recursive_program,
        );
    }
    pub fn new(program: Program) -> Self {
        let mut processed: RelationStorage = Default::default();

        let unprocessed_insertions: RelationStorage = Default::default();
        let unprocessed_deletions: RelationStorage = Default::default();

        let delta_program = make_delta_program(&program, true);

        let mut relations = HashSet::new();
        let mut delta_relations = HashSet::new();

        delta_program.inner.iter().for_each(|rule| {
            relations.insert(&rule.head.symbol);
            delta_relations.insert(format!("{}{}", DELTA_PREFIX, rule.head.symbol));

            rule.body.iter().for_each(|body_atom| {
                relations.insert(&body_atom.symbol);
                delta_relations.insert(format!("{}{}", DELTA_PREFIX, body_atom.symbol));
            })
        });

        relations.iter().for_each(|relation_symbol| {
            processed
                .inner
                .entry(relation_symbol.to_string())
                .or_default();
        });

        delta_relations.iter().for_each(|relation_symbol| {
            processed
                .inner
                .entry(relation_symbol.to_string())
                .or_default();
        });

        let (nonrecursive_program, recursive_program) = split_program(delta_program);

        Self {
            processed,
            unprocessed_insertions,
            unprocessed_deletions,
            program,
            nonrecursive_program,
            recursive_program,
        }
    }
    pub fn safe(&self) -> bool {
        self.unprocessed_insertions.len() == 0
    }
}

#[cfg(test)]
mod tests {
    fn test_runtime() {}
}
