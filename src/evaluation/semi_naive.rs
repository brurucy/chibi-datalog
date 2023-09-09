use crate::engine::storage::RelationStorage;
use crate::helpers::helpers::{DELTA_PREFIX, split_program};
use crate::program_transformations::delta_program::make_delta_program;
use datalog_syntax::Program;

pub fn semi_naive_evaluation(fact_storage: &mut RelationStorage, program: &Program, update: bool) {
    // TODO plop this out of this function
    let delta_program = make_delta_program(program, update);
    delta_program.inner.iter().for_each(|rule| {
        fact_storage
                .inner
                .entry(rule.head.symbol.clone())
                .or_default();

        if rule.head.symbol.contains(DELTA_PREFIX) {
            fact_storage
                .inner
                .entry(rule.head.symbol.strip_prefix(DELTA_PREFIX).unwrap().to_string())
                .or_default();
        }
    });
    // TODO this too
    let (nonrecursive_program, recursive_program) = split_program(delta_program);

    fact_storage.materialize_delta_program(&nonrecursive_program);

    loop {
        let previous_non_delta_fact_count = fact_storage.len();

        fact_storage.materialize_delta_program(&recursive_program);

        let current_non_delta_fact_count = fact_storage.len();

        let new_fact_count = current_non_delta_fact_count - previous_non_delta_fact_count;

        if new_fact_count == 0 {
            return;
        }
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashSet;
    use datalog_rule_macro::program;
    use datalog_syntax::*;
    use crate::engine::storage::RelationStorage;
    use crate::evaluation::semi_naive::semi_naive_evaluation;

    #[test]
    fn test_one_hop_initial() {
        let mut storage: RelationStorage = Default::default();
        storage.inner.insert("e".to_string(), Default::default());
        storage
            .inner
            .get_mut("e")
            .unwrap()
            .insert(vec!["a".into(), "b".into()]);
        storage
            .inner
            .get_mut("e")
            .unwrap()
            .insert(vec!["b".into(), "c".into()]);

        let one_hop = program! { hop(?x, ?z) <- [e(?x, ?y), e(?y, ?z)] };

        let expected: HashSet<AnonymousGroundAtom> = vec![vec!["a".into(), "c".into()]].into_iter().collect();
        semi_naive_evaluation(&mut storage, &one_hop, false);
        let actual: HashSet<_> = storage.get_relation("hop").unwrap().into_iter().cloned().collect();

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_linear_tc_initial() {
        let mut storage: RelationStorage = Default::default();
        storage.inner.insert("e".to_string(), Default::default());
        storage
            .inner
            .get_mut("e")
            .unwrap()
            .insert(vec!["a".into(), "b".into()]);
        storage
            .inner
            .get_mut("e")
            .unwrap()
            .insert(vec!["b".into(), "c".into()]);
        storage
            .inner
            .get_mut("e")
            .unwrap()
            .insert(vec!["c".into(), "d".into()]);


        let tc_program = program!{
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)],
        };

        let expected: HashSet<AnonymousGroundAtom> = vec![
            // First iter
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
            // Second iter
            vec!["a".into(), "c".into()],
            vec!["b".into(), "d".into()],
            // Third iter
            vec!["a".into(), "d".into()],
        ].into_iter().collect();
        semi_naive_evaluation(&mut storage, &tc_program, false);
        let actual: HashSet<_> = storage.get_relation("tc").unwrap().into_iter().cloned().collect();

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_nonlinear_tc_initial() {
        let mut storage: RelationStorage = Default::default();
        storage.inner.insert("e".to_string(), Default::default());
        storage
            .inner
            .get_mut("e")
            .unwrap()
            .insert(vec!["a".into(), "b".into()]);
        storage
            .inner
            .get_mut("e")
            .unwrap()
            .insert(vec!["b".into(), "c".into()]);
        storage
            .inner
            .get_mut("e")
            .unwrap()
            .insert(vec!["c".into(), "d".into()]);

        let tc_program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)],
        };

        let expected: HashSet<AnonymousGroundAtom> = vec![
            // First iter
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
            // Second iter
            vec!["a".into(), "c".into()],
            vec!["b".into(), "d".into()],
            // Third iter
            vec!["a".into(), "d".into()],
        ].into_iter().collect();
        semi_naive_evaluation(&mut storage, &tc_program, false);
        let actual: HashSet<_> = storage.get_relation("tc").unwrap().into_iter().cloned().collect();

        assert_eq!(expected, actual);
    }
}
