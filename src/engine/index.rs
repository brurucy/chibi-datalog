use crate::engine::program_index::UniqueColumnCombinations;
use crate::engine::rewrite::{InternedAtom, InternedTerm};
use crate::engine::storage::RelationStorage;
use crate::helpers::helpers::{add_prefix, DELTA_PREFIX};
use crate::interning::fact_registry::{FactRegistry, Row};
use ahash::{AHasher, HashMap, HashMapExt};
use dashmap::DashMap;
use rayon::prelude::*;
use std::hash::{Hash, Hasher};

fn hashisher<K: Hash>(key: &Vec<K>) -> Row {
    let mut hasher = AHasher::default();

    key.iter()
        .for_each(|masked_value| masked_value.hash(&mut hasher));

    Row(hasher.finish())
}

pub fn mask_atom(atom: &InternedAtom) -> Row {
    let mut hasher = AHasher::default();

    atom.terms
        .iter()
        .map(|term| match term {
            InternedTerm::Constant(value) => Some(value),
            _ => None,
        })
        .for_each(|masked_value| masked_value.hash(&mut hasher));

    Row(hasher.finish())
}

pub type MaskedRowToRows = DashMap<Row, Vec<Row>>;

pub type IndexedRepresentation = HashMap<String, HashMap<Vec<usize>, MaskedRowToRows>>;

fn index(
    unique_column_combinations: &UniqueColumnCombinations,
    facts_by_relation: &RelationStorage,
    fact_registry: &FactRegistry,
) -> IndexedRepresentation {
    let mut results: IndexedRepresentation = HashMap::new();

    let flattened_uccs: Vec<(String, Vec<usize>, MaskedRowToRows)> = unique_column_combinations
        .iter()
        .fold(vec![], |mut acc, (curr_sym, curr_uccs)| {
            curr_uccs.into_iter().for_each(|ucc| {
                acc.push((curr_sym.clone(), ucc.clone(), MaskedRowToRows::default()));
            });

            acc
        });

    let index: Vec<_> = flattened_uccs
        .into_par_iter()
        .map(|(sym, ucc, ucc_index)| {
            if !ucc.is_empty() {
                if let Some(hashes) = facts_by_relation.inner.get(&sym) {
                    for hash in hashes {
                        let fact = fact_registry.get(*hash);
                        let mut projected_row = vec![None; fact.len()];

                        for &column_index in &ucc {
                            if column_index < fact.len() {
                                projected_row[column_index] = Some(&fact[column_index]);
                            }
                        }

                        let mut current_masked_atoms =
                            ucc_index.entry(hashisher(&projected_row)).or_default();
                        current_masked_atoms.push(*hash);
                    }
                }
            }

            (sym, ucc, ucc_index)
        })
        .collect();

    index.into_iter().for_each(|(sym, ucc, ucc_index)| {
        let sym_uccs = results.entry(sym).or_default();
        let ucc_projections = sym_uccs.entry(ucc).or_default();

        *ucc_projections = ucc_index;
    });

    results
}

pub struct Index {
    pub inner: IndexedRepresentation,
}

impl<'a> Index {
    pub fn new(
        relation_storage: &'a RelationStorage,
        uccs: &'a UniqueColumnCombinations,
        fact_registry: &'a FactRegistry,
    ) -> Self {
        let inner = index(&uccs, relation_storage, fact_registry);

        return Self { inner };
    }
    pub(crate) fn update(
        &mut self,
        unique_column_combinations: &UniqueColumnCombinations,
        facts_by_relation: &RelationStorage,
        fact_registry: &FactRegistry,
    ) {
        unique_column_combinations
            .iter()
            .for_each(|(symbol, uccs)| {
                // Clearing all deltas in the index
                if symbol.starts_with(DELTA_PREFIX) {
                    let current_relation_entry = self.inner.entry(symbol.clone()).or_default();

                    uccs.iter().for_each(|delta_ucc| {
                        let current_delta_ucc_entry =
                            current_relation_entry.entry(delta_ucc.clone()).or_default();
                        current_delta_ucc_entry.clear();
                    })
                }
                // Else we assure that all other relation/ucc combinations exist
                else {
                    let current_relation_entry = self.inner.entry(symbol.clone()).or_default();
                    uccs.iter().for_each(|ucc| {
                        current_relation_entry.entry(ucc.clone()).or_default();
                    })
                }
            });

        let flattened_uccs: Vec<(String, Vec<usize>)> =
            unique_column_combinations
                .iter()
                .fold(vec![], |mut acc, (curr_sym, curr_uccs)| {
                    curr_uccs
                        .into_iter()
                        .for_each(|ucc| acc.push((curr_sym.clone(), ucc.clone())));

                    acc
                });

        flattened_uccs.into_par_iter().for_each(|(sym, ucc)| {
            let mut local_symbol = sym.clone();
            if !local_symbol.starts_with(DELTA_PREFIX) {
                add_prefix(&mut local_symbol, DELTA_PREFIX);
            };
            if !ucc.is_empty() {
                let ucc_index = self.inner.get(&sym).unwrap().get(&ucc).unwrap();

                if let Some(hashes) = facts_by_relation.inner.get(&local_symbol) {
                    hashes.par_iter().chunks(16384).for_each(|chunk| {
                        chunk.into_iter().for_each(|hash| {
                            let fact = fact_registry.get(*hash);
                            let mut projected_row = vec![None; fact.len()];

                            for &column_index in &ucc {
                                if column_index < fact.len() {
                                    projected_row[column_index] = Some(&fact[column_index]);
                                }
                            }

                            let mut current_masked_atoms =
                                ucc_index.entry(hashisher(&projected_row)).or_default();
                            current_masked_atoms.push(*hash);
                        })
                    })
                }
            }
        });
    }
}

#[cfg(test)]
mod tests {
    /*use crate::engine::index::unique_column_combinations;
    use ahash::HashMap;
    use datalog_rule_macro::rule;
    use datalog_syntax::*;

    #[test]
    fn test_ucc() {
        // Using the `rule!` macro to define a rule.
        let my_rule = rule! { tc(?x, ?y) <- [e(?x, ?y), e(?y, ?z)] };

        let expected: HashMap<String, Vec<Vec<usize>>> = vec![
            ("e".to_string(), vec![vec![], vec![0]]), // For e(?x, ?y), both ?x and ?y are seen for the first time.
        ]
        .into_iter()
        .collect();

        // Run the `unique_column_combinations` function and compare to expected.
        let (actual, _) = unique_column_combinations(&my_rule);

        assert_eq!(actual, expected);
    }*/

    // #[test]
    /*fn test_index() {
        let unique_column_combinations: HashMap<String, Vec<Vec<usize>>> = vec![
            ("relation1".to_string(), vec![vec![0]]), // Project on first column.
            ("relation2".to_string(), vec![vec![1]]), // Project on second column.
        ]
        .into_iter()
        .collect();

        let mut storage = RelationStorage::default();
        let one: TypedValue = 1.into();
        let three: TypedValue = 3.into();
        let six: TypedValue = 6.into();
        let eight: TypedValue = 8.into();
        vec![vec![one.clone(), 2.into()], vec![three.clone(), 4.into()]]
            .into_iter()
            .for_each(|anonymous_atom| {
                storage.insert("relation1", anonymous_atom);
            });

        vec![vec![5.into(), six.clone()], vec![7.into(), eight.clone()]]
            .into_iter()
            .for_each(|anonymous_atom| {
                storage.insert("relation2", anonymous_atom);
            });

        // Expected results after join and projection.
        let relation_1_indexes: HashMap<Vec<usize>, Vec<MaskedAtom>> = vec![(
            vec![0],
            vec![vec![Some(&one), None], vec![Some(&three), None]],
        )]
        .into_iter()
        .collect();

        let relation_2_indexes: HashMap<Vec<usize>, Vec<MaskedAtom>> = vec![(
            vec![1],
            vec![vec![None, Some(&six)], vec![None, Some(&eight)]],
        )]
        .into_iter()
        .collect();

        let expected: HashMap<String, HashMap<Vec<usize>, Vec<MaskedAtom>>> = vec![
            ("relation1".to_string(), relation_1_indexes),
            ("relation2".to_string(), relation_2_indexes),
        ]
        .into_iter()
        .collect();

        let actual = join_and_project_facts(&unique_column_combinations, &storage.inner);
        actual
            .into_iter()
            .for_each(|(symbol, positions_masked_atoms)| {
                positions_masked_atoms
                    .into_iter()
                    .for_each(|(position, masked_atom)| {
                        let actual_masked_atom_set: HashSet<_> = masked_atom.into_iter().collect();
                        let expected_masked_atom_set: HashSet<_> = expected
                            .get(&symbol)
                            .unwrap()
                            .get(&position)
                            .unwrap()
                            .into_iter()
                            .cloned()
                            .collect();

                        assert_eq!(expected_masked_atom_set, actual_masked_atom_set)
                    });
            });
    }*/
}
