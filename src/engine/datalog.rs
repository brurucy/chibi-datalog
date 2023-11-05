use crate::engine::storage::RelationStorage;
use crate::evaluation::query::pattern_match;
use crate::evaluation::semi_naive::semi_naive_evaluation;
use crate::helpers::helpers::{
    add_prefix, split_program, DELTA_PREFIX, OVERDELETION_PREFIX, REDERIVATION_PREFIX,
};
use crate::program_transformations::delta_program::make_delta_program;
use crate::program_transformations::dred::{make_overdeletion_program, make_rederivation_program};
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
    fn remove(&mut self, query: &Query) {
        self.processed
            .inner
            .get(query.symbol)
            .unwrap()
            .iter()
            .for_each(|fact| {
                if pattern_match(query, fact) {
                    self.unprocessed_deletions.insert(
                        &format!("{}{}", OVERDELETION_PREFIX, query.symbol),
                        fact.clone(),
                    );
                }
            })
    }
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
        if !self.unprocessed_deletions.is_empty() {
            // Deletions
            self.unprocessed_deletions.drain_all_relations().for_each(
                |(relation_symbol, unprocessed_facts)| {
                    let mut overdeletion_symbol = relation_symbol.clone();
                    add_prefix(&mut overdeletion_symbol, OVERDELETION_PREFIX);

                    self.processed
                        .insert_all(&overdeletion_symbol, unprocessed_facts.into_iter());
                },
            );

            let overdeletion_program =
                make_delta_program(&make_overdeletion_program(&self.program), false);
            let (nonrecursive_overdeletion_program, recursive_overdeletion_program) =
                split_program(overdeletion_program);

            // Overdeletion computation
            semi_naive_evaluation(
                &mut self.processed,
                &nonrecursive_overdeletion_program,
                &recursive_overdeletion_program,
            );
            self.processed.drain_deltas();
            // Physical overdeletion...might be better to just mark as deleted.
            self.processed.overdelete();

            // Rederivation
            let overdeletion_program =
                make_delta_program(&make_rederivation_program(&self.program), false);
            let (nonrecursive_rederivation_program, recursive_rederivation_program) =
                split_program(overdeletion_program);

            // Rederivation computation
            semi_naive_evaluation(
                &mut self.processed,
                &nonrecursive_rederivation_program,
                &recursive_rederivation_program,
            );
            self.processed.drain_deltas();
            // Physical rederivation
            self.processed.rederive();

            self.processed.clear_prefix(OVERDELETION_PREFIX);
            self.processed.clear_prefix(REDERIVATION_PREFIX);
        }
        if !self.unprocessed_insertions.is_empty() {
            // Additions
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

            self.processed.drain_deltas()
        }
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
    use crate::engine::datalog::ChibiRuntime;
    use datalog_rule_macro::program;
    use datalog_syntax::*;
    use std::collections::HashSet;

    #[test]
    fn integration_test_insertions_only() {
        let tc_program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)],
        };

        let mut runtime = ChibiRuntime::new(tc_program);
        vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
        ]
        .into_iter()
        .for_each(|edge| {
            runtime.insert("e", edge);
        });

        runtime.poll();

        // This query reads as: "Get all in tc with any values in any positions: tc(_, _, _)"
        let mut select_all_in_tc = QueryBuilder::new("tc");
        select_all_in_tc.with_any();
        select_all_in_tc.with_any();
        select_all_in_tc.with_any();
        let all: Query = select_all_in_tc.into();

        // tc(a, _, _)
        let mut select_all_reachable_from_a = QueryBuilder::new("tc");
        select_all_reachable_from_a.with_constant("a".into());
        select_all_reachable_from_a.with_any();
        select_all_reachable_from_a.with_any();
        let all_from_a: Query = select_all_reachable_from_a.into();

        let actual_all: HashSet<&AnonymousGroundAtom> = runtime.query(&all).unwrap().collect();
        let expected_all: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
            // Second iter
            vec!["a".into(), "c".into()],
            vec!["b".into(), "d".into()],
            // Third iter
            vec!["a".into(), "d".into()],
        ]
        .into_iter()
        .collect();
        assert_eq!(expected_all, actual_all.into_iter().cloned().collect());

        let actual_all_from_a = runtime.query(&all_from_a).unwrap();
        let expected_all_from_a: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["a".into(), "c".into()],
            vec!["a".into(), "d".into()],
        ]
        .into_iter()
        .collect();
        assert_eq!(
            expected_all_from_a,
            actual_all_from_a.into_iter().cloned().collect()
        );

        expected_all.iter().for_each(|fact| {
            assert!(runtime.contains("tc", fact).unwrap());
        });

        expected_all_from_a.iter().for_each(|fact| {
            assert!(runtime.contains("tc", fact).unwrap());
        });

        // Update
        runtime.insert("tc", vec!["d".into(), "e".into()]);
        assert!(!runtime.safe());
        runtime.poll();
        assert!(runtime.safe());

        let actual_all_after_update: HashSet<&AnonymousGroundAtom> =
            runtime.query(&all).unwrap().collect();
        let expected_all_after_update: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
            // Second iter
            vec!["a".into(), "c".into()],
            vec!["b".into(), "d".into()],
            // Third iter
            vec!["a".into(), "d".into()],
            // Update
            vec!["d".into(), "e".into()],
            vec!["c".into(), "e".into()],
            vec!["b".into(), "e".into()],
            vec!["a".into(), "e".into()],
        ]
        .into_iter()
        .collect();
        assert_eq!(
            expected_all_after_update,
            actual_all_after_update.into_iter().cloned().collect()
        );

        let actual_all_from_a_after_update = runtime.query(&all_from_a).unwrap();
        let expected_all_from_a_after_update: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["a".into(), "c".into()],
            vec!["a".into(), "d".into()],
            vec!["a".into(), "e".into()],
        ]
        .into_iter()
        .collect();
        assert_eq!(
            expected_all_from_a_after_update,
            actual_all_from_a_after_update
                .into_iter()
                .cloned()
                .collect()
        );
    }
    fn integration_test_deletions() {}
}
