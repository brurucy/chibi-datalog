use crate::engine::rewrite::{InternedAtom, InternedTerm};
use crate::engine::storage::RelationStorage;
use crate::helpers::helpers::{add_prefix, DELTA_PREFIX};
use ahash::{AHasher, HashMap, HashMapExt, HashSet};
use ascent::internal::Instant;
use datalog_syntax::AnonymousGroundAtom;
use lazy_static::lazy_static;
use rayon::prelude::*;
use std::hash::{Hash, Hasher};
use std::sync::Mutex;

pub type UniqueColumnCombinations = HashMap<String, HashSet<Vec<usize>>>;

fn hashisher<K: Hash>(key: &Vec<K>) -> usize {
    let mut hasher = AHasher::default();

    key.iter()
        .for_each(|masked_value| masked_value.hash(&mut hasher));

    hasher.finish() as usize
}

pub fn mask_atom(atom: &InternedAtom) -> usize {
    let mut hasher = AHasher::default();

    atom.terms
        .iter()
        .map(|term| match term {
            InternedTerm::Constant(value) => Some(value),
            _ => None,
        })
        //.for_each(|masked_value| masked_atom.push(masked_value));
        .for_each(|masked_value| masked_value.hash(&mut hasher));

    hasher.finish() as usize
}

lazy_static! {
    static ref FACT_REGISTRY: Mutex<HashSet<&'static AnonymousGroundAtom>> = {
        let mut hm = Mutex::new(HashSet::default());

        hm
    };
}

fn register_atom(atom: &AnonymousGroundAtom) -> &'static AnonymousGroundAtom {
    let mut fregistry = FACT_REGISTRY.lock().unwrap();

    return match fregistry.get(atom) {
        None => {
            let boxed_atom = Box::new(atom.clone());
            let leaked_boxed_atom: &'static AnonymousGroundAtom = Box::leak(boxed_atom);
            fregistry.insert(leaked_boxed_atom);

            leaked_boxed_atom
        }
        Some(inner) => *inner,
    };
}

/*pub struct IndexedRepresentation<'a> {
    inner: HashMap<String, HashMap<Vec<usize>, HashMap<usize, HashSet<AnonymousGroundAtom>>>>,
    fact_storage: &'a mut RelationStorage,
}*/

pub type IndexedRepresentation =
    HashMap<String, HashMap<Vec<usize>, HashMap<usize, HashSet<&'static AnonymousGroundAtom>>>>;

fn index(
    unique_column_combinations: &UniqueColumnCombinations,
    facts_by_relation: &RelationStorage,
) -> IndexedRepresentation {
    let mut results: IndexedRepresentation = HashMap::new();

    /*let now = Instant::now();
    facts_by_relation.inner.iter().for_each(|(sym, facts)| {
        facts.iter().for_each(|fact| {
            register_atom(fact);
        })
    });
    println!("registration: {} micros", now.elapsed().as_micros());*/

    let flattened_uccs: Vec<(
        String,
        Vec<usize>,
        HashMap<usize, HashSet<&'static AnonymousGroundAtom>>,
    )> = unique_column_combinations
        .iter()
        .fold(vec![], |mut acc, (curr_sym, curr_uccs)| {
            curr_uccs.into_iter().for_each(|ucc| {
                acc.push((curr_sym.clone(), ucc.clone(), HashMap::default()));
            });

            acc
        });

    let index: Vec<_> = flattened_uccs
        .into_par_iter()
        .map(|(sym, ucc, mut ucc_index)| {
            if !ucc.is_empty() {
                if let Some(facts) = facts_by_relation.inner.get(&sym) {
                    for fact in facts {
                        let mut projected_row = vec![None; fact.len()];

                        // Perform the projection using the unique columns.
                        for &column_index in &ucc {
                            if column_index < fact.len() {
                                projected_row[column_index] = Some(&fact[column_index]);
                            }
                        }

                        let current_masked_atoms =
                            ucc_index.entry(hashisher(&projected_row)).or_default();

                        current_masked_atoms.insert(register_atom(fact));
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
    pub ucc: UniqueColumnCombinations,
}

impl<'a> Index {
    pub fn new(relation_storage: &'a RelationStorage, uccs: UniqueColumnCombinations) -> Self {
        let inner = index(&uccs, relation_storage);

        return Self { inner, ucc: uccs };
    }
    pub fn update(
        &mut self,
        facts_by_relation: &RelationStorage,
        update_ucc: &UniqueColumnCombinations,
    ) {
        let flattened_uccs: Vec<(
            String,
            Vec<usize>,
            HashMap<usize, HashSet<&'a AnonymousGroundAtom>>,
        )> = update_ucc
            .iter()
            .fold(vec![], |mut acc, (curr_sym, curr_uccs)| {
                curr_uccs.into_iter().for_each(|ucc| {
                    acc.push((curr_sym.clone(), ucc.clone(), HashMap::default()));
                });

                acc
            });

        // Invalidating delta indexes
        for (symbol, uccs) in update_ucc {
            let current_relation_entry = self.inner.entry(symbol.clone()).or_default();
            let is_delta = symbol.starts_with(DELTA_PREFIX);
            if is_delta {
                uccs.iter().for_each(|delta_ucc| {
                    current_relation_entry.remove(delta_ucc);
                });
            };
        }

        flattened_uccs
            .into_par_iter()
            .map(|(sym, ucc, mut ucc_index)| {
                let mut local_sym = sym.clone();
                let is_delta = sym.starts_with(DELTA_PREFIX);
                if !is_delta {
                    add_prefix(&mut local_sym, DELTA_PREFIX);
                }

                if !ucc.is_empty() {
                    if let Some(facts) = facts_by_relation.inner.get(&local_sym) {
                        for fact in facts {
                            let mut projected_row = vec![None; fact.len()];

                            // Perform the projection using the unique columns.
                            for &column_index in &ucc {
                                if column_index < fact.len() {
                                    projected_row[column_index] = Some(&fact[column_index]);
                                }
                            }

                            let current_masked_atoms =
                                ucc_index.entry(hashisher(&projected_row)).or_default();
                            current_masked_atoms.insert(fact);
                        }
                    }
                }

                (sym, ucc, ucc_index)
            })
            .collect::<Vec<_>>()
            .into_iter()
            .for_each(|(sym, ucc, ucc_index)| {
                let sym_uccs = self.inner.entry(sym).or_default();
                let ucc_projections = sym_uccs.entry(ucc).or_default();

                ucc_index
                    .into_iter()
                    .for_each(|(projection, fact_references)| {
                        let projection_mappings = ucc_projections.entry(projection).or_default();

                        projection_mappings
                            .extend(fact_references.into_iter().map(|fact| register_atom(fact)));
                    });
            });

        /*for (symbol, uccs) in update_ucc {
            let current_relation_entry = self.inner.entry(symbol.clone()).or_default();
            let is_delta = symbol.starts_with(DELTA_PREFIX);
            if is_delta {
                uccs.iter().for_each(|delta_ucc| {
                    current_relation_entry.remove(delta_ucc);
                });
            };

            let mut local_symbol = symbol.clone();
            if !is_delta {
                add_prefix(&mut local_symbol, DELTA_PREFIX);
            };

            let now = Instant::now();
            uccs.iter().for_each(|ucc| {
                let current_relation_ucc = current_relation_entry.entry(ucc.clone()).or_default();
                if !ucc.is_empty() {
                    if let Some(facts) = facts_by_relation.inner.get(&local_symbol) {
                        for fact in facts {
                            let mut projected_row = vec![None; fact.len()];

                            // Perform the projection using the unique columns.
                            for &column_index in ucc {
                                if column_index < fact.len() {
                                    projected_row[column_index] = Some(&fact[column_index]);
                                }
                            }

                            let current_masked_atoms = current_relation_ucc
                                .entry(hashisher(&projected_row))
                                .or_default();

                            current_masked_atoms.insert(register_atom(&fact));
                        }
                    }
                }
            });
            println!(
                "time to update relation {} uccs {:?}: {} milis",
                symbol,
                uccs,
                now.elapsed().as_millis()
            );
        }*/
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
