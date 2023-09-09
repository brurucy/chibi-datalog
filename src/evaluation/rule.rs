use crate::engine::rewrite::{unify, Rewrite};
use crate::engine::storage::RelationStorage;
use datalog_syntax::{AnonymousGroundAtom, Program, Rule};

pub struct RuleEvaluator<'a> {
    rule: &'a Rule,
    facts_storage: &'a RelationStorage,
    rewrites: Vec<Rewrite>,
}

impl<'a> RuleEvaluator<'a> {
    pub(crate) fn new(facts_storage: &'a RelationStorage, rule: &'a Rule) -> Self {
        Self {
            rule,
            facts_storage,
            rewrites: vec![Rewrite::default()],
        }
    }
}

impl<'a> RuleEvaluator<'a> {
    // Doing it depth-first might warrant better results with iterators, since computation
    // would emit facts faster than breadth-first (which defers until all of them are ready to be
    // emitted)
    pub fn step(&mut self) -> impl Iterator<Item = AnonymousGroundAtom> + 'a {
        let mut current_rewrites = self.rewrites.clone();

        for current_body_atom in self.rule.body.iter() {
            let current_unification_targets: Vec<_> = current_rewrites
                .clone()
                .into_iter()
                .map(|rewrite| (rewrite.apply(current_body_atom), rewrite))
                .collect();

            current_rewrites.clear();
            if let Some(relation) = self.facts_storage.get_relation(&current_body_atom.symbol) {
                relation.iter().for_each(|current_ground_atom| {
                    current_unification_targets
                        .iter()
                        .for_each(|(unification_target, rewrite)| {
                            if let Some(new_rewrite) =
                                unify(unification_target, current_ground_atom)
                            {
                                let mut local_rewrite = rewrite.clone().clone();
                                local_rewrite.extend(new_rewrite);

                                current_rewrites.push(local_rewrite);
                            };
                        })
                });
            };
        }

        current_rewrites
            .into_iter()
            .map(|rewrite| rewrite.ground(self.rule.head.clone()))
    }
}