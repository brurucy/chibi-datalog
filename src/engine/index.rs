use crate::engine::program_index::UniqueColumnCombinations;
use crate::engine::rewrite::{InternedAtom, InternedTerm};
use crate::engine::storage::RelationStorage;
use crate::interning::fact_registry::{hashisher, FactRegistry, Row};
use ahash::{HashMap, HashMapExt, HashSet};
use ascent::internal::Instant;
use datalog_syntax::{AnonymousGroundAtom, TypedValue};
use rayon::prelude::*;
use std::hash::Hasher;

pub fn mask_atom(atom: &InternedAtom) -> Row {
    let mut masked_atom = vec![];

    atom.terms
        .iter()
        .map(|term| match term {
            InternedTerm::Constant(value) => Some(value),
            _ => None,
        })
        .for_each(|masked_value| masked_atom.push(masked_value));

    hashisher(&masked_atom)
}

pub type MaskedAtom<'a> = Vec<Option<&'a TypedValue>>;

pub type IndexedRepresentation = HashMap<String, HashMap<Vec<usize>, HashMap<Row, HashSet<Row>>>>;

fn index(
    unique_column_combinations: &UniqueColumnCombinations,
    facts_by_relation: &RelationStorage,
    fact_registry: &FactRegistry,
) -> IndexedRepresentation {
    let mut results: IndexedRepresentation = HashMap::new();

    let unique_column_combinations: UniqueColumnCombinations = unique_column_combinations
        .iter()
        .map(|(symbol, ucc_set)| {
            (
                symbol.clone(),
                ucc_set
                    .into_iter()
                    .map(|ucc| {
                        let mut ucc = ucc.clone();
                        ucc.sort();

                        ucc
                    })
                    .collect::<HashSet<_>>(),
            )
        })
        .collect();

    let now = Instant::now();
    let flattened_uccs: Vec<(&String, &Vec<usize>, MaskedAtom, HashSet<Row>)> =
        unique_column_combinations
            .iter()
            .fold(vec![], |mut acc, (curr_sym, curr_uccs)| {
                curr_uccs.into_iter().for_each(|ucc| {
                    let masked_facts: HashSet<_> = facts_by_relation
                        .inner
                        .get(curr_sym)
                        .unwrap()
                        .iter()
                        .map(|fact| {
                            let fact = fact_registry.get(*fact);

                            let mut projected_fact = vec![None; fact.len()];

                            // Perform the projection using the unique columns.
                            for &column_index in ucc {
                                if column_index < fact.len() {
                                    projected_fact[column_index] = Some(&fact[column_index]);
                                }
                            }

                            projected_fact
                        })
                        .collect();

                    masked_facts.into_iter().for_each(|masked_fact| {
                        acc.push((curr_sym, ucc, masked_fact, HashSet::default()));
                    })
                });

                acc
            });
    println!("Flattening: {} milis", now.elapsed().as_millis());

    // Example:
    // Sym - UCC    - Mask   - Data
    // e   - [1, 2] - [b, c] - [a, b, c], [d, b, c], ...
    // e   - [0, 1] - [a, b] - [a, b, c], [a, b, d], ...
    // T   - [0]    - [a]    - [a, b, c], [a, b, d], ...
    let now = Instant::now();
    let ucc_count = flattened_uccs.len();
    println!("uccs: {}", ucc_count);
    let tchunkz = ucc_count / 8;
    let index: Vec<_> = flattened_uccs
        .par_chunks(tchunkz)
        .flat_map(|chunk| {
            chunk
                .into_iter()
                .map(|(sym, ucc, masked_row, mut ucc_index)| {
                    if !ucc.is_empty() {
                        if let Some(hashes) = facts_by_relation.inner.get(*sym) {
                            hashes.iter().for_each(|hash| {
                                let fact = fact_registry.get(*hash);

                                let mut projected_fact = vec![None; fact.len()];

                                // Perform the projection using the unique columns.
                                for column_index in *ucc {
                                    if *column_index < fact.len() {
                                        projected_fact[*column_index] = Some(&fact[*column_index]);
                                    }
                                }

                                if projected_fact == *masked_row {
                                    ucc_index.insert(*hash);
                                }
                            });
                        }
                    }

                    (sym, ucc, masked_row, ucc_index)
                })
                .collect::<Vec<_>>()
        })
        .collect();
    println!("actual index building: {} ms", now.elapsed().as_millis());
    /*let index: Vec<_> = flattened_uccs
    .into_par_iter()
    .map(|(sym, ucc, mut ucc_index)| {
        if !ucc.is_empty() {
            if let Some(hashes) = facts_by_relation.inner.get(&sym) {
                hashes.iter().for_each(|hash| {
                    let fact = fact_registry.get(*hash);
                    let mut projected_row = vec![None; fact.len()];

                    // Perform the projection using the unique columns.
                    for &column_index in &ucc {
                        if column_index < fact.len() {
                            projected_row[column_index] = Some(&fact[column_index]);
                        }
                    }

                    let mut current_masked_atoms =
                        ucc_index.entry(hashisher(&projected_row)).or_default();
                    current_masked_atoms.insert(*hash);
                });
            }
        }

        (sym, ucc, ucc_index)
    })
    .collect();*/

    index
        .into_iter()
        .for_each(|(sym, ucc, masked_row, ucc_index)| {
            let sym_uccs = results.entry(sym.to_string()).or_default();
            let ucc_projections = sym_uccs.entry(ucc.clone().clone()).or_default();
            let row_set = ucc_projections.entry(hashisher(&masked_row)).or_default();

            *row_set = ucc_index.clone();
        });

    results
}

fn update(
    unique_column_combinations: &UniqueColumnCombinations,
    facts_by_relation: &RelationStorage,
    fact_registry: &FactRegistry,
) {
    let mut results: IndexedRepresentation = HashMap::new();

    let flattened_uccs: Vec<(String, Vec<usize>, HashMap<usize, HashSet<Row>>)> =
        unique_column_combinations
            .iter()
            .fold(vec![], |mut acc, (curr_sym, curr_uccs)| {
                curr_uccs.into_iter().for_each(|ucc| {
                    acc.push((curr_sym.clone(), ucc.clone(), HashMap::default()));
                });

                acc
            });
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
