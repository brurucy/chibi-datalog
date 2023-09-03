use datalog_syntax::*;
use crate::engine::storage::RelationStorage;

pub struct ChibiRuntime {
    storage: RelationStorage,
    program: Program,
}

impl ChibiRuntime {
    fn insert(&mut self, relation: &str, ground_atom: AnonymousGroundAtom) {
        unimplemented!()
    }
    /*fn remove(&mut self, query: &Query) {
        unimplemented!()
    }
    fn contains(&self, relation: &str, ground_atom: &GroundAtom) {
        unimplemented!()
    }*/
    fn poll() {
        unimplemented!()
    }
    /*fn query(&self, query: &Query) {
        unimplemented!()
    }*/
    fn new_with_program(program: Vec<Rule>) -> Self {
        Self {
            storage: Default::default(),
            program,
        }
    }
}

#[cfg(test)]
mod test {
    use crate::engine::datalog::{RuleEvaluator, RelationStorage};
    use datalog_rule_macro::rule;
    use datalog_syntax::*;

    #[test]
    fn rule() {
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

        let one_hop = rule! { hop(?x, ?z) <- [e(?x, ?y), e(?y, ?z)] };

        let mut rule_evaluator = RuleEvaluator::new(&storage, &one_hop);

        let expected: Vec<AnonymousGroundAtom> = vec![vec!["a".into(), "c".into()]];
        let actual: Vec<_> = rule_evaluator.step().collect();

        assert_eq!(expected, actual);
    }
}
