use crate::engine::index::{mask_atom, Index};
use crate::engine::program_index::JoinOrder;
use crate::engine::rewrite::{intern_rule, unify, Rewrite};
use crate::engine::storage::RelationStorage;
use crate::interning::fact_registry::FactRegistry;
use ascent::internal::Instant;
use datalog_syntax::{AnonymousGroundAtom, Rule};
use rayon::prelude::*;

pub struct RuleEvaluator<'a> {
    rule: &'a Rule,
    facts_storage: &'a RelationStorage,
    join_order: &'a JoinOrder,
    index: &'a Index,
    fact_registry: &'a FactRegistry,
}

impl<'a> RuleEvaluator<'a> {
    pub(crate) fn new(
        facts_storage: &'a RelationStorage,
        rule: &'a Rule,
        join_order: &'a JoinOrder,
        index: &'a Index,
        fact_registry: &'a FactRegistry,
    ) -> Self {
        Self {
            rule,
            facts_storage,
            join_order,
            index,
            fact_registry,
        }
    }
}

impl<'a> RuleEvaluator<'a> {
    // Doing it depth-first might warrant better results with iterators, since computation
    // would emit facts faster than breadth-first (which defers until all of them are ready to be
    // emitted)
    pub fn step(&self) -> impl Iterator<Item = AnonymousGroundAtom> + 'a {
        let join_sequence = self.join_order;

        let (interned_rule, id_translator) = intern_rule(self.rule.clone());

        // Perhaps a trie is warranted. There is a lot of repetition
        let mut current_rewrites: Vec<Rewrite> = vec![Rewrite::default()];

        for (current_body_atom, join_key) in
            interned_rule.body.iter().zip(join_sequence.into_iter())
        {
            let mut new_rewrites = boxcar::vec![];
            current_rewrites
                .drain(..)
                .par_bridge()
                //.with_min_len(10000)
                .map(|rewrite| (rewrite.apply(current_body_atom), rewrite))
                .for_each(|(unification_target, rewrite)| {
                    // If it is empty, then this is the first body atom. In this case, do a join.
                    if join_key.is_empty() {
                        let current_relation = self
                            .facts_storage
                            .get_relation(id_translator.get(&unification_target.symbol).unwrap());

                        current_relation
                            .into_par_iter()
                            .for_each(|current_ground_atom| {
                                if let Some(new_rewrite) = unify(
                                    &unification_target,
                                    self.fact_registry.get(*current_ground_atom),
                                ) {
                                    let mut local_rewrite = rewrite.clone();
                                    local_rewrite.extend(new_rewrite);

                                    new_rewrites.push(local_rewrite);
                                };
                            });
                    } else {
                        let matches_by_symbol = self
                            .index
                            .inner
                            .get(id_translator.get(&current_body_atom.symbol).unwrap())
                            .unwrap();
                        let matches_by_positions = matches_by_symbol.get(join_key).unwrap();

                        let masked_atom = mask_atom(&unification_target);
                        if let Some(matches_by_mask) = matches_by_positions.get(&masked_atom) {
                            matches_by_mask.par_iter().for_each(|current_ground_atom| {
                                let new_rewrite = unify(
                                    &unification_target,
                                    self.fact_registry.get(*current_ground_atom),
                                )
                                .unwrap();

                                let mut local_rewrite = rewrite.clone();
                                local_rewrite.extend(new_rewrite);

                                new_rewrites.push(local_rewrite);
                            });
                        }
                    }
                });

            current_rewrites = new_rewrites.into_iter().collect();
        }

        current_rewrites
            .into_iter()
            .map(move |rewrite| rewrite.ground(&interned_rule.head))
    }
}
