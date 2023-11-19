use crate::engine::index::{mask_atom, Index};
use crate::engine::program_index::JoinOrder;
use crate::engine::rewrite::{intern_rule, unify, Rewrite};
use crate::engine::storage::RelationStorage;
use crate::interning::fact_registry::FactRegistry;
use ascent::internal::Instant;
use datalog_syntax::{AnonymousGroundAtom, Rule};

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
        let join_sequence: Vec<_> = self
            .join_order
            .iter()
            .map(|join_key| {
                let mut local_join_key = join_key.clone();
                local_join_key.sort();

                return local_join_key;
            })
            .collect();

        let (interned_rule, id_translator) = intern_rule(self.rule.clone());

        // Perhaps a trie is warranted. There is a lot of repetition
        let mut current_rewrites: Vec<Rewrite> = vec![Rewrite::default()];

        for (current_body_atom, join_key) in
            interned_rule.body.iter().zip(join_sequence.into_iter())
        {
            let mut new_rewrites = vec![];
            let now = Instant::now();
            current_rewrites
                .drain(..)
                .map(|rewrite| (rewrite.apply(current_body_atom), rewrite))
                .for_each(|(unification_target, rewrite)| {
                    // If it is empty, then this is the first body atom. In this case, do a join.
                    if join_key.is_empty() {
                        let current_relation = self
                            .facts_storage
                            .get_relation(id_translator.get(&unification_target.symbol).unwrap())
                            .unwrap();

                        current_relation.iter().for_each(|current_ground_atom| {
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
                        if let Some(matches_by_symbol) = self
                            .index
                            .inner
                            .get(id_translator.get(&current_body_atom.symbol).unwrap())
                        {
                            if let Some(matches_by_position) = matches_by_symbol.get(&join_key) {
                                let masked_atom = mask_atom(&unification_target);
                                if let Some(matches_by_mask) = matches_by_position.get(&masked_atom)
                                {
                                    matches_by_mask.iter().for_each(|current_ground_atom| {
                                        if let Some(new_rewrite) = unify(
                                            &unification_target,
                                            self.fact_registry.get(*current_ground_atom),
                                        ) {
                                            let mut local_rewrite = rewrite.clone();
                                            local_rewrite.extend(new_rewrite);

                                            new_rewrites.push(local_rewrite);
                                        };
                                    });
                                }
                            }
                        }
                    }
                });

            current_rewrites = new_rewrites.into_iter().collect();
            if join_key.is_empty() {
                println!(
                    "first iteration: {} milis, {:?} {:?}",
                    now.elapsed().as_millis(),
                    join_key,
                    current_body_atom.symbol
                );
            }
        }

        current_rewrites
            .into_iter()
            .map(move |rewrite| rewrite.ground(&interned_rule.head))
    }
}
