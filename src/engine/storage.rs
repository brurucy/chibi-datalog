use crate::engine::index::Index;
use crate::engine::program_index::RuleJoinOrders;
use crate::evaluation::rule::RuleEvaluator;
use crate::helpers::helpers::{DELTA_PREFIX, OVERDELETION_PREFIX, REDERIVATION_PREFIX};
use crate::interning::fact_registry::{FactRegistry, Row};
use dashmap::{DashMap, Map};
use datalog_syntax::{AnonymousGroundAtom, Program};
use indexmap::IndexSet;
use rayon::prelude::*;

pub type FactStorage = IndexSet<Row, ahash::RandomState>;
#[derive(Default)]
pub struct RelationStorage {
    pub(crate) inner: DashMap<String, FactStorage>,
    pub(crate) fact_registry: FactRegistry,
}

impl RelationStorage {
    pub fn get_relation(&self, relation_symbol: &str) -> &FactStorage {
        let shard = self.inner.determine_map(relation_symbol);
        let shard_map = unsafe { self.inner._get_read_shard(shard) };

        return shard_map.get(relation_symbol).unwrap().get();
    }
    pub fn drain_relation(&self, relation_symbol: &str) -> Vec<Row> {
        let mut rel = self.inner.get_mut(relation_symbol).unwrap();

        return rel.drain(..).collect();
    }
    pub fn drain_all_relations(
        &mut self,
    ) -> impl Iterator<Item = (String, Vec<(Row, AnonymousGroundAtom)>)> + '_ {
        let relations_to_be_drained: Vec<_> =
            self.inner.iter().map(|pair| pair.key().clone()).collect();

        relations_to_be_drained.into_iter().map(|relation_symbol| {
            (
                relation_symbol.clone(),
                self.inner
                    .get_mut(&relation_symbol)
                    .unwrap()
                    .drain(..)
                    .map(|hash| (hash, self.fact_registry.remove(hash)))
                    .collect::<Vec<_>>(),
            )
        })
    }
    pub fn drain_prefix_filter<'a>(
        &'a mut self,
        prefix: &'a str,
    ) -> impl Iterator<Item = (String, Vec<Row>)> + '_ {
        let relations_to_be_drained: Vec<_> = self
            .inner
            .iter()
            .map(|pair| pair.key().clone())
            .filter(|relation_symbol| relation_symbol.starts_with(prefix))
            .collect();

        relations_to_be_drained.into_iter().map(|relation_symbol| {
            (
                relation_symbol.clone(),
                self.inner
                    .get_mut(&relation_symbol)
                    .unwrap()
                    .drain(..)
                    .collect::<Vec<_>>(),
            )
        })
    }
    pub fn drain_deltas(&mut self) {
        let delta_relation_symbols: Vec<_> = self
            .inner
            .iter()
            .map(|pair| pair.key().clone())
            .filter(|relation_symbol| relation_symbol.starts_with(DELTA_PREFIX))
            .collect();

        delta_relation_symbols
            .into_iter()
            .for_each(|relation_symbol| {
                if relation_symbol.starts_with(DELTA_PREFIX) {
                    let delta_facts: Vec<_> = self.drain_relation(&relation_symbol);

                    let mut current_non_delta_relation = self
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
            .filter(|ref_multi| ref_multi.key().starts_with(OVERDELETION_PREFIX))
            .map(|ref_multi| {
                (
                    ref_multi.key().clone(),
                    ref_multi
                        .key()
                        .strip_prefix(&OVERDELETION_PREFIX)
                        .unwrap()
                        .to_string(),
                )
            })
            .collect();

        overdeletion_relations.into_iter().for_each(
            |(overdeletion_symbol, actual_relation_symbol)| {
                let overdeletion_relation = self.inner.remove(&overdeletion_symbol).unwrap();
                let mut actual_relation = self.inner.get_mut(&actual_relation_symbol).unwrap();

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
            .filter(|ref_multi| ref_multi.key().starts_with(REDERIVATION_PREFIX))
            .map(|ref_multi| {
                (
                    ref_multi.key().clone(),
                    ref_multi
                        .key()
                        .strip_prefix(&REDERIVATION_PREFIX)
                        .unwrap()
                        .to_string(),
                )
            })
            .collect();

        rederivation_relations.into_iter().for_each(
            |(rederivation_symbol, actual_relation_symbol)| {
                let rederivation_relation = self.inner.remove(&rederivation_symbol).unwrap();
                let mut actual_relation = self.inner.get_mut(&actual_relation_symbol).unwrap();

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
        self.inner.iter_mut().for_each(|mut ref_mult| {
            let (symbol, relation) = ref_mult.pair_mut();

            if symbol.starts_with(prefix) {
                relation.clear()
            }
        });
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

        if let Some(mut relation) = self.inner.get_mut(relation_symbol) {
            relation.extend(hashes)
        } else {
            let mut fresh_fact_storage = FactStorage::default();
            fresh_fact_storage.extend(hashes);

            self.inner
                .insert(relation_symbol.to_string(), fresh_fact_storage);
        }
    }

    pub fn insert_all(&self, relation_symbol: &str, facts: impl Iterator<Item = Row>) {
        if let Some(mut relation) = self.inner.get_mut(relation_symbol) {
            relation.extend(facts.into_iter())
        } else {
            let mut fresh_fact_storage = FactStorage::default();
            fresh_fact_storage.extend(facts.into_iter());

            self.inner
                .insert(relation_symbol.to_string(), fresh_fact_storage);
        }
    }
    pub fn register(&mut self, fact: AnonymousGroundAtom) {
        self.fact_registry.register(fact);
    }
    pub fn insert(&mut self, relation_symbol: &str, ground_atom: AnonymousGroundAtom) -> bool {
        if let Some(mut relation) = self.inner.get_mut(relation_symbol) {
            return relation.insert(self.fact_registry.register(ground_atom));
        }

        let mut fresh_fact_storage = FactStorage::default();
        fresh_fact_storage.insert(self.fact_registry.register(ground_atom));

        self.inner
            .insert(relation_symbol.to_string(), fresh_fact_storage);

        true
    }
    pub fn remove(&mut self, relation_symbol: &str, ground_atom: AnonymousGroundAtom) -> bool {
        if let Some(mut relation) = self.inner.get_mut(relation_symbol) {
            let registration = &self.fact_registry.register(ground_atom);

            return relation.remove(registration);
        }

        false
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

        let evaluation = evaluation_setup
            .into_par_iter()
            .map(|(delta_relation_symbol, rule)| {
                (delta_relation_symbol, rule.step().collect::<Vec<_>>())
            })
            .collect::<Vec<_>>();

        evaluation.into_iter().enumerate().for_each(
            |(idx, (delta_relation_symbol, current_delta_evaluation))| {
                let self_mut_ref = self as *mut Self;

                let curr = self.get_relation(delta_relation_symbol);

                let diff: FactStorage = current_delta_evaluation
                    .into_iter()
                    .map(|fact| unsafe {
                        let self_ref = &mut *self_mut_ref;

                        self_ref.fact_registry.register(fact)
                    })
                    .filter(|row| !curr.contains(row))
                    .collect();

                // This is actually wrong :) it will blow up at some point....
                if idx == 0 {
                    (*self.inner.get_mut(delta_relation_symbol).unwrap()) = diff.clone();
                } else {
                    self.insert_all(delta_relation_symbol, diff.clone().into_iter());
                }

                let relation_symbol = delta_relation_symbol.clone();
                relation_symbol.strip_prefix(DELTA_PREFIX).unwrap();
                self.insert_all(
                    delta_relation_symbol.strip_prefix(DELTA_PREFIX).unwrap(),
                    diff.into_iter(),
                );
            },
        );
    }

    pub fn len(&self) -> usize {
        return self
            .inner
            .iter()
            .filter(|ref_multi| !ref_multi.key().starts_with(DELTA_PREFIX))
            .map(|ref_multi| ref_multi.value().len())
            .sum();
    }

    pub fn is_empty(&self) -> bool {
        return self.len() == 0;
    }
}
