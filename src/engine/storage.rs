use crate::engine::index::Index;
use crate::engine::program_index::RuleJoinOrders;
use crate::evaluation::rule::RuleEvaluator;
use crate::helpers::helpers::{DELTA_PREFIX, OVERDELETION_PREFIX, REDERIVATION_PREFIX};
use crate::interning::fact_registry::{FactRegistry, Row};
use ahash::{HashMap, HashSet};
use datalog_syntax::{AnonymousGroundAtom, Program};
use indexmap::IndexSet;
use rayon::prelude::*;
use std::time::Instant;

pub type FactStorage = IndexSet<Row, ahash::RandomState>;
#[derive(Default)]
pub struct RelationStorage {
    pub(crate) inner: HashMap<String, FactStorage>,
    pub(crate) fact_registry: FactRegistry,
}

impl RelationStorage {
    pub fn get_relation(&self, relation_symbol: &str) -> Option<&FactStorage> {
        return self.inner.get(relation_symbol);
    }
    pub fn drain_relation(&mut self, relation_symbol: &str) -> impl Iterator<Item = Row> + '_ {
        self.inner.get_mut(relation_symbol).unwrap().drain(..)
    }
    pub fn drain_all_relations(
        &mut self,
    ) -> impl Iterator<Item = (&String, Vec<(Row, AnonymousGroundAtom)>)> + '_ {
        self.inner.iter_mut().map(|(relation_symbol, facts)| {
            (
                relation_symbol,
                facts
                    .drain(..)
                    .map(|hash| (hash, self.fact_registry.remove(hash)))
                    .collect::<Vec<_>>(),
            )
        })
    }
    pub fn drain_prefix_filter<'a>(
        &'a mut self,
        prefix: &'a str,
    ) -> impl Iterator<Item = (&String, Vec<Row>)> + '_ {
        return self
            .inner
            .iter_mut()
            .filter(move |(relation_symbol, _)| relation_symbol.contains(prefix))
            .map(|(relation_symbol, facts)| {
                (relation_symbol, facts.drain(..).collect::<Vec<_>>())
            });
    }
    pub fn drain_deltas(&mut self) {
        let delta_relation_symbols: Vec<_> = self
            .inner
            .keys()
            .filter(|relation_symbol| relation_symbol.starts_with(DELTA_PREFIX))
            .cloned()
            .collect();

        delta_relation_symbols
            .into_iter()
            .for_each(|relation_symbol| {
                if relation_symbol.starts_with(DELTA_PREFIX) {
                    let delta_facts: Vec<_> = self.drain_relation(&relation_symbol).collect();

                    let current_non_delta_relation = self
                        .inner
                        .get_mut(relation_symbol.strip_prefix(DELTA_PREFIX).unwrap())
                        .unwrap();

                    delta_facts.into_iter().for_each(|fact| {
                        current_non_delta_relation.insert(fact);
                    });
                }
            });
    }
    pub fn overdelete(&mut self) {
        let overdeletion_relations: Vec<_> = self
            .inner
            .iter()
            .filter(|(symbol, _)| symbol.starts_with(OVERDELETION_PREFIX))
            .map(|(symbol, _)| {
                (
                    symbol.clone(),
                    symbol
                        .strip_prefix(&OVERDELETION_PREFIX)
                        .unwrap()
                        .to_string(),
                )
            })
            .collect();

        overdeletion_relations.into_iter().for_each(
            |(overdeletion_symbol, actual_relation_symbol)| {
                let overdeletion_relation = self.inner.remove_entry(&overdeletion_symbol).unwrap();
                let actual_relation = self.inner.get_mut(&actual_relation_symbol).unwrap();

                overdeletion_relation.1.iter().for_each(|atom| {
                    actual_relation.remove(atom);
                });

                // We insert it back because it is necessary for rederivation.
                self.inner
                    .insert(overdeletion_relation.0, overdeletion_relation.1);
            },
        );
    }
    pub fn rederive(&mut self) {
        let rederivation_relations: Vec<_> = self
            .inner
            .iter()
            .filter(|(symbol, _)| symbol.starts_with(REDERIVATION_PREFIX))
            .map(|(symbol, _)| {
                (
                    symbol.clone(),
                    symbol
                        .strip_prefix(&REDERIVATION_PREFIX)
                        .unwrap()
                        .to_string(),
                )
            })
            .collect();

        rederivation_relations.into_iter().for_each(
            |(rederivation_symbol, actual_relation_symbol)| {
                let rederivation_relation = self.inner.remove_entry(&rederivation_symbol).unwrap();
                let actual_relation = self.inner.get_mut(&actual_relation_symbol).unwrap();

                rederivation_relation.1.into_iter().for_each(|atom| {
                    actual_relation.insert(atom);
                });
            },
        );
    }
    pub fn clear_relation(&mut self, relation_symbol: &str) {
        self.inner.get_mut(relation_symbol).unwrap().clear();
    }
    pub fn clear_prefix(&mut self, prefix: &str) {
        for (symbol, relation) in self.inner.iter_mut() {
            if symbol.starts_with(prefix) {
                relation.clear();
            }
        }
    }

    pub fn insert_registered(
        &mut self,
        relation_symbol: &str,
        registrations: impl Iterator<Item = (Row, AnonymousGroundAtom)>,
    ) {
        let mut hashes = vec![];

        registrations.into_iter().for_each(|(hash, fact)| {
            self.fact_registry.insert_registered(hash, fact);

            hashes.push(hash);
        });

        if let Some(relation) = self.inner.get_mut(relation_symbol) {
            relation.extend(hashes)
        } else {
            let mut fresh_fact_storage = FactStorage::default();
            fresh_fact_storage.extend(hashes);

            self.inner
                .insert(relation_symbol.to_string(), fresh_fact_storage);
        }
    }

    pub fn insert_all(
        &mut self,
        relation_symbol: &str,
        facts: impl Iterator<Item = AnonymousGroundAtom>,
    ) {
        if let Some(relation) = self.inner.get_mut(relation_symbol) {
            relation.extend(
                facts
                    .into_iter()
                    .map(|fact| self.fact_registry.register(fact)),
            )
        } else {
            let mut fresh_fact_storage = FactStorage::default();
            fresh_fact_storage.extend(
                facts
                    .into_iter()
                    .map(|fact| self.fact_registry.register(fact)),
            );

            self.inner
                .insert(relation_symbol.to_string(), fresh_fact_storage);
        }
    }
    pub fn register(&mut self, fact: AnonymousGroundAtom) {
        self.fact_registry.register(fact);
    }
    pub fn insert(&mut self, relation_symbol: &str, ground_atom: AnonymousGroundAtom) -> bool {
        if let Some(relation) = self.inner.get_mut(relation_symbol) {
            return relation.insert(self.fact_registry.register(ground_atom));
        }

        let mut fresh_fact_storage = FactStorage::default();
        fresh_fact_storage.insert(self.fact_registry.register(ground_atom));

        self.inner
            .insert(relation_symbol.to_string(), fresh_fact_storage);

        true
    }
    pub fn contains(&self, relation_symbol: &str, ground_atom: &AnonymousGroundAtom) -> bool {
        if let Some(relation) = self.inner.get(relation_symbol) {
            return relation.contains(&self.fact_registry.compute_key(ground_atom));
        }

        false
    }

    pub fn materialize_delta_program(
        &mut self,
        program: &Program,
        rule_join_orders: &RuleJoinOrders,
        index: &Index,
    ) {
        let evaluation_setup: Vec<_> = program
            .inner
            .iter()
            .map(|rule| {
                (
                    &rule.head.symbol,
                    RuleEvaluator::new(
                        self,
                        rule,
                        rule_join_orders.get(&rule.id).unwrap(),
                        &index,
                        &self.fact_registry,
                    ),
                )
            })
            .collect();

        let now = Instant::now();
        let evaluation = evaluation_setup
            .into_par_iter()
            .map(|(delta_relation_symbol, rule)| {
                (delta_relation_symbol, rule.step().collect::<HashSet<_>>())
            })
            .collect::<Vec<_>>();
        println!("evaluation time: {} milis", now.elapsed().as_millis());

        let relations_to_clear: HashSet<_> =
            evaluation.iter().map(|(sym, _)| sym).cloned().collect();
        relations_to_clear.iter().for_each(|delta_relation_symbol| {
            self.clear_relation(delta_relation_symbol);
        });

        let now = Instant::now();
        evaluation
            .into_iter()
            .for_each(|(delta_relation_symbol, current_delta_evaluation)| {
                let relation_symbol = delta_relation_symbol.clone();
                relation_symbol.strip_prefix(DELTA_PREFIX).unwrap();
                let current_delta_relation_hashes = self.inner.get(delta_relation_symbol).unwrap();

                let diff: Vec<_> = current_delta_evaluation
                    .into_iter()
                    .filter(|inferred_fact| {
                        if self.fact_registry.contains(inferred_fact) {
                            let key = self.fact_registry.compute_key(inferred_fact);

                            return !current_delta_relation_hashes.contains(&key);
                        }

                        true
                    })
                    .collect();

                /*let diff: Vec<_> = current_delta_evaluation
                .difference(self.get_relation(delta_relation_symbol).unwrap())
                .cloned()
                .collect();*/

                self.insert_all(delta_relation_symbol, diff.clone().into_iter()); //diff.clone().into_iter());

                self.insert_all(
                    delta_relation_symbol.strip_prefix(DELTA_PREFIX).unwrap(),
                    //diff.into_iter(),
                    diff.into_iter(),
                );
            });
        println!("post-evaluation: {} milis", now.elapsed().as_millis());
    }

    pub fn len(&self) -> usize {
        return self
            .inner
            .iter()
            .filter(|(symbol, _)| !symbol.starts_with(DELTA_PREFIX))
            .map(|(_, relation)| relation.len())
            .sum();
    }

    pub fn is_empty(&self) -> bool {
        return self.len() == 0;
    }
}
