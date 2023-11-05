use crate::engine::storage::RelationStorage;
use datalog_syntax::Program;

pub fn semi_naive_evaluation(
    fact_storage: &mut RelationStorage,
    nonrecursive_delta_program: &Program,
    recursive_delta_program: &Program,
) {
    fact_storage.materialize_delta_program(&nonrecursive_delta_program);

    loop {
        let previous_non_delta_fact_count = fact_storage.len();

        fact_storage.materialize_delta_program(&recursive_delta_program);

        let current_non_delta_fact_count = fact_storage.len();

        let new_fact_count = current_non_delta_fact_count - previous_non_delta_fact_count;

        if new_fact_count == 0 {
            return;
        }
    }
}

#[cfg(test)]
mod test {
    use crate::engine::storage::RelationStorage;
    use crate::evaluation::semi_naive::semi_naive_evaluation;
    use crate::helpers::helpers::split_program;
    use crate::program_transformations::delta_program::make_delta_program;
    use datalog_rule_macro::program;
    use datalog_syntax::*;
    use std::collections::HashSet;

    fn insert_into(
        storage: &mut RelationStorage,
        relation_symbol: &str,
        facts: Vec<AnonymousGroundAtom>,
    ) {
        facts.into_iter().for_each(|fact| {
            storage.inner.get_mut(relation_symbol).unwrap().insert(fact);
        });
    }

    #[test]
    fn test_one_hop() {
        let mut storage: RelationStorage = Default::default();
        storage.inner.insert("e".to_string(), Default::default());
        storage.inner.insert("Δe".to_string(), Default::default());
        storage.inner.insert("hop".to_string(), Default::default());
        storage.inner.insert("Δhop".to_string(), Default::default());
        insert_into(
            &mut storage,
            "e",
            vec![vec!["a".into(), "b".into()], vec!["b".into(), "c".into()]],
        );
        insert_into(
            &mut storage,
            "Δe",
            vec![vec!["a".into(), "b".into()], vec!["b".into(), "c".into()]],
        );

        let one_hop = program! { hop(?x, ?z) <- [e(?x, ?y), e(?y, ?z)] };
        let (nonrecursive_delta_program, recursive_delta_program) =
            split_program(make_delta_program(&one_hop, true));

        let expected: HashSet<AnonymousGroundAtom> =
            vec![vec!["a".into(), "c".into()]].into_iter().collect();
        semi_naive_evaluation(
            &mut storage,
            &nonrecursive_delta_program,
            &recursive_delta_program,
        );
        let actual: HashSet<_> = storage
            .get_relation("hop")
            .unwrap()
            .into_iter()
            .cloned()
            .collect();

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_linear_tc() {
        let mut storage: RelationStorage = Default::default();
        storage.inner.insert("e".to_string(), Default::default());
        storage.inner.insert("Δe".to_string(), Default::default());
        storage.inner.insert("tc".to_string(), Default::default());
        storage.inner.insert("Δtc".to_string(), Default::default());

        insert_into(
            &mut storage,
            "e",
            vec![
                vec!["a".into(), "b".into()],
                vec!["b".into(), "c".into()],
                vec!["c".into(), "d".into()],
            ],
        );
        insert_into(
            &mut storage,
            "Δe",
            vec![
                vec!["a".into(), "b".into()],
                vec!["b".into(), "c".into()],
                vec!["c".into(), "d".into()],
            ],
        );

        let tc_program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)],
        };
        let (nonrecursive_delta_program, recursive_delta_program) =
            split_program(make_delta_program(&tc_program, true));

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
        ]
        .into_iter()
        .collect();

        semi_naive_evaluation(
            &mut storage,
            &nonrecursive_delta_program,
            &recursive_delta_program,
        );

        let actual: HashSet<_> = storage
            .get_relation("tc")
            .unwrap()
            .into_iter()
            .cloned()
            .collect();

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_nonlinear_tc() {
        let mut storage: RelationStorage = Default::default();
        storage.inner.insert("e".to_string(), Default::default());
        storage.inner.insert("Δe".to_string(), Default::default());
        storage.inner.insert("tc".to_string(), Default::default());
        storage.inner.insert("Δtc".to_string(), Default::default());

        insert_into(
            &mut storage,
            "e",
            vec![
                vec!["a".into(), "b".into()],
                vec!["b".into(), "c".into()],
                vec!["c".into(), "d".into()],
            ],
        );
        insert_into(
            &mut storage,
            "Δe",
            vec![
                vec!["a".into(), "b".into()],
                vec!["b".into(), "c".into()],
                vec!["c".into(), "d".into()],
            ],
        );

        let tc_program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)],
        };
        let (nonrecursive_delta_program, recursive_delta_program) =
            split_program(make_delta_program(&tc_program, true));

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
        ]
        .into_iter()
        .collect();
        semi_naive_evaluation(
            &mut storage,
            &nonrecursive_delta_program,
            &recursive_delta_program,
        );

        let actual: HashSet<_> = storage
            .get_relation("tc")
            .unwrap()
            .into_iter()
            .cloned()
            .collect();

        assert_eq!(expected, actual);
    }
}
