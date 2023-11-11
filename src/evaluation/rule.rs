use crate::engine::index::{mask_atom, Index};
use crate::engine::program_index::JoinOrder;
use crate::engine::rewrite::{intern_rule, unify, Rewrite};
use crate::engine::storage::RelationStorage;
use datalog_syntax::{AnonymousGroundAtom, Rule};
use std::time;
use time::Instant;

pub struct RuleEvaluator<'a> {
    rule: &'a Rule,
    facts_storage: &'a RelationStorage,
    join_order: &'a JoinOrder,
    index: &'a Index<'a>,
}

impl<'a> RuleEvaluator<'a> {
    pub(crate) fn new(
        facts_storage: &'a RelationStorage,
        rule: &'a Rule,
        join_order: &'a JoinOrder,
        index: &'a Index,
    ) -> Self {
        Self {
            rule,
            facts_storage,
            join_order,
            index,
        }
    }
}

impl<'a> RuleEvaluator<'a> {
    // Doing it depth-first might warrant better results with iterators, since computation
    // would emit facts faster than breadth-first (which defers until all of them are ready to be
    // emitted)
    pub fn step(&self) -> impl Iterator<Item = AnonymousGroundAtom> + 'a {
        let join_sequence = self.join_order;

        //let mut now = Instant::now();
        //let index = Index::new(self.facts_storage, &self.global_uccs);
        //println!("indexing time: {}", now.elapsed().as_micros());
        let (interned_rule, id_translator) = intern_rule(self.rule.clone());

        // Perhaps a trie is warranted. There is a lot of repetition
        let mut current_rewrites: Vec<Rewrite> = vec![Rewrite::default()];

        for (current_body_atom, join_key) in
            interned_rule.body.iter().zip(join_sequence.into_iter())
        {
            let matches_by_symbol = self
                .index
                .inner
                .get(id_translator.get(&current_body_atom.symbol).unwrap())
                .unwrap();
            let matches_by_positions = matches_by_symbol.get(join_key).unwrap();

            let mut new_rewrites = vec![];
            current_rewrites
                .drain(..)
                .map(|rewrite| (rewrite.apply(current_body_atom), rewrite))
                .into_iter()
                .for_each(|(unification_target, rewrite)| {
                    // If it is empty, then this is the first body atom.
                    if join_key.is_empty() {
                        let current_relation = self
                            .facts_storage
                            .get_relation(id_translator.get(&unification_target.symbol).unwrap())
                            .unwrap();

                        current_relation.iter().for_each(|current_ground_atom| {
                            if let Some(new_rewrite) =
                                unify(&unification_target, current_ground_atom)
                            {
                                let mut local_rewrite = rewrite.clone();
                                local_rewrite.extend(new_rewrite);

                                new_rewrites.push(local_rewrite);
                            };
                        });
                    } else {
                        let masked_atom = mask_atom(&unification_target);
                        if let Some(matches_by_mask) = matches_by_positions.get(&masked_atom) {
                            matches_by_mask.iter().for_each(|current_ground_atom| {
                                let new_rewrite =
                                    unify(&unification_target, current_ground_atom).unwrap();

                                let mut local_rewrite = rewrite.clone();
                                local_rewrite.extend(new_rewrite);

                                new_rewrites.push(local_rewrite);
                            });
                        }
                    }
                });

            current_rewrites = new_rewrites;
        }

        current_rewrites
            .into_iter()
            .map(move |rewrite| rewrite.ground(&interned_rule.head))
    }
}
