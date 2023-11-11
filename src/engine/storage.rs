use crate::engine::index::{Index, UniqueColumnCombinations};
use crate::engine::program_index::{ProgramIndex, RuleJoinOrders};
use crate::evaluation::rule::RuleEvaluator;
use crate::helpers::helpers::{DELTA_PREFIX, OVERDELETION_PREFIX, REDERIVATION_PREFIX};
use ahash::HashSetExt;
use datalog_syntax::{AnonymousGroundAtom, Program};
use rayon::prelude::*;
use std::collections::HashMap;
use std::time::Instant;

pub type FactStorage = ahash::HashSet<AnonymousGroundAtom>;
#[derive(Default)]
pub struct RelationStorage {
    pub(crate) inner: HashMap<String, FactStorage>,
}

impl RelationStorage {
    pub fn get_relation(&self, relation_symbol: &str) -> Option<&FactStorage> {
        return self.inner.get(relation_symbol);
    }
    pub fn drain_relation(
        &mut self,
        relation_symbol: &str,
    ) -> impl Iterator<Item = AnonymousGroundAtom> + '_ {
        self.inner.get_mut(relation_symbol).unwrap().drain()
    }
    pub fn drain_all_relations(
        &mut self,
    ) -> impl Iterator<Item = (&String, Vec<AnonymousGroundAtom>)> + '_ {
        self.inner
            .iter_mut()
            .map(|(relation_symbol, facts)| (relation_symbol, facts.drain().collect::<Vec<_>>()))
    }
    pub fn drain_prefix_filter<'a>(
        &'a mut self,
        prefix: &'a str,
    ) -> impl Iterator<Item = (&String, Vec<AnonymousGroundAtom>)> + '_ {
        return self
            .inner
            .iter_mut()
            .filter(move |(relation_symbol, _)| relation_symbol.contains(prefix))
            .map(|(relation_symbol, facts)| (relation_symbol, facts.drain().collect::<Vec<_>>()));
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

    pub fn insert_all(
        &mut self,
        relation_symbol: &str,
        facts: impl Iterator<Item = AnonymousGroundAtom>,
    ) {
        if let Some(relation) = self.inner.get_mut(relation_symbol) {
            relation.extend(facts)
        } else {
            let mut fresh_fact_storage = FactStorage::new();
            fresh_fact_storage.extend(facts);

            self.inner
                .insert(relation_symbol.to_string(), fresh_fact_storage);
        }
    }
    pub fn insert(&mut self, relation_symbol: &str, ground_atom: AnonymousGroundAtom) -> bool {
        if let Some(relation) = self.inner.get_mut(relation_symbol) {
            return relation.insert(ground_atom);
        }

        let mut fresh_fact_storage = FactStorage::new();
        fresh_fact_storage.insert(ground_atom);

        self.inner
            .insert(relation_symbol.to_string(), fresh_fact_storage);

        true
    }
    pub fn contains(&self, relation_symbol: &str, ground_atom: &AnonymousGroundAtom) -> bool {
        if let Some(relation) = self.inner.get(relation_symbol) {
            return relation.contains(ground_atom);
        }

        false
    }

    pub fn materialize_delta_program(
        &mut self,
        program: &Program,
        rule_join_orders: &RuleJoinOrders,
        global_uccs: &UniqueColumnCombinations,
    ) {
        let now = Instant::now();

        let program_local_uccs = ProgramIndex::from(vec![program]);
        let index = Index::new(
            &self,
            &program_local_uccs.unique_program_column_combinations,
        );
        println!("indexing time: {}", now.elapsed().as_micros());

        let evaluation_setup: Vec<_> = program
            .inner
            .iter()
            .map(|rule| {
                (
                    &rule.head.symbol,
                    RuleEvaluator::new(self, rule, rule_join_orders.get(&rule.id).unwrap(), &index),
                )
            })
            .collect();

        let now = Instant::now();
        let evaluation = evaluation_setup
            .into_iter()
            .map(|(delta_relation_symbol, rule)| {
                (delta_relation_symbol, rule.step().collect::<Vec<_>>())
            })
            .collect::<Vec<_>>();
        println!("evaluation time: {}", now.elapsed().as_micros());

        evaluation.iter().for_each(|(delta_relation_symbol, _)| {
            self.clear_relation(delta_relation_symbol);
        });

        let now = Instant::now();
        evaluation
            .into_iter()
            .for_each(|(delta_relation_symbol, facts)| {
                self.insert_all(delta_relation_symbol, facts.clone().into_iter());

                self.insert_all(
                    delta_relation_symbol.strip_prefix(DELTA_PREFIX).unwrap(),
                    facts.into_iter(),
                );
            });
        //println!("postsert time: {}", now.elapsed().as_micros());
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
