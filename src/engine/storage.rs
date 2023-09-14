use crate::evaluation::rule::RuleEvaluator;
use crate::helpers::helpers::DELTA_PREFIX;
use datalog_syntax::{AnonymousGroundAtom, Program};
use std::collections::{HashMap, HashSet};

pub type FactStorage = HashSet<AnonymousGroundAtom>;
#[derive(Default)]
pub struct RelationStorage {
    pub(crate) inner: HashMap<String, FactStorage>,
}

impl RelationStorage {
    pub fn get_relation(&self, relation_symbol: &str) -> Option<&HashSet<AnonymousGroundAtom>> {
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
    pub fn clear_relation(&mut self, relation_symbol: &str) {
        self.inner.get_mut(relation_symbol).unwrap().clear();
    }
    pub fn drain_deltas(&mut self) {
        let delta_relation_symbols: Vec<_> = self
            .inner
            .keys()
            .filter(|relation_symbol| relation_symbol.contains(DELTA_PREFIX))
            .cloned()
            .collect();

        delta_relation_symbols
            .into_iter()
            .for_each(|relation_symbol| {
                if relation_symbol.contains(DELTA_PREFIX) {
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

    pub fn materialize_delta_program(&mut self, program: &Program) {
        let mut evaluation: Vec<_> = program
            .inner
            .iter()
            .map(|rule| (&rule.head.symbol, RuleEvaluator::new(self, rule)))
            .map(|(delta_relation_symbol, mut rule)| {
                (delta_relation_symbol, rule.step().collect::<Vec<_>>())
            })
            .collect();

        evaluation
            .iter_mut()
            .for_each(|(delta_relation_symbol, _)| {
                self.clear_relation(delta_relation_symbol);
            });

        evaluation
            .into_iter()
            .for_each(|(delta_relation_symbol, facts)| {
                self.insert_all(delta_relation_symbol, facts.clone().into_iter());

                self.insert_all(
                    delta_relation_symbol.strip_prefix(DELTA_PREFIX).unwrap(),
                    facts.clone().into_iter(),
                );
            });
    }

    pub fn len(&self) -> usize {
        return self
            .inner
            .iter()
            .filter(|(symbol, _)| !symbol.contains(DELTA_PREFIX))
            .map(|(_, relation)| relation.len())
            .sum();
    }
}
