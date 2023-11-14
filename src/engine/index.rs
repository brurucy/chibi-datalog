use crate::engine::program_index::UniqueColumnCombinations;
use crate::engine::rewrite::{InternedAtom, InternedTerm};
use crate::engine::storage::RelationStorage;
use ahash::{AHasher, HashMap, HashMapExt, HashSet};
use datalog_syntax::{AnonymousGroundAtom, TypedValue};
use std::hash::{Hash, Hasher};

pub type MaskedAtom<'a> = Vec<Option<&'a TypedValue>>;

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
        .for_each(|masked_value| masked_value.hash(&mut hasher));

    hasher.finish() as usize
}

pub type IndexedRepresentation<'a> =
    HashMap<String, HashMap<Vec<usize>, HashMap<usize, HashSet<&'a AnonymousGroundAtom>>>>;

fn index<'a>(
    unique_column_combinations: &UniqueColumnCombinations,
    facts_by_relation: &'a RelationStorage,
) -> IndexedRepresentation<'a> {
    let mut results: IndexedRepresentation<'a> = HashMap::new();

    let mut total = 0;
    let mut useless = 0;
    for (symbol, uccs) in unique_column_combinations.iter() {
        let current_relation_entry = results.entry(symbol.clone()).or_default();
        uccs.iter().for_each(|ucc| {
            let current_ucc_entry = current_relation_entry.entry(ucc.clone()).or_default();

            // It is pointless to index empty join keys, since it will just clone the whole relation instead of a column subset
            if !ucc.is_empty() {
                if let Some(facts) = facts_by_relation.inner.get(symbol) {
                    for fact in facts {
                        let mut projected_row = vec![None; fact.len()];

                        // Perform the projection using the unique columns.
                        for &column_index in ucc {
                            if column_index < fact.len() {
                                projected_row[column_index] = Some(&fact[column_index]);
                            }
                        }

                        let current_masked_atoms = current_ucc_entry
                            .entry(hashisher(&projected_row))
                            .or_default();
                        total += 1;
                        let wasteful = current_masked_atoms.insert(fact);
                        if !wasteful {
                            useless += 1;
                        }
                    }
                }
            }
        });
    }

    println!("total: {}, wasteful: {}", total, useless);
    results.iter().for_each(|(sym, outer)| {
        outer.iter().for_each(|(positions, contents)| {
            println!(
                "sym: {}, position: {:?}, quantity: {}",
                sym,
                positions,
                contents
                    .values()
                    .into_iter()
                    .map(|hs| hs.len())
                    .sum::<usize>(),
            )
        });
    });

    results
}

pub struct Index<'a> {
    pub inner: IndexedRepresentation<'a>,
}

impl<'a> Index<'a> {
    pub fn new(relation_storage: &'a RelationStorage, uccs: &UniqueColumnCombinations) -> Self {
        let inner = index(&uccs, relation_storage);

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
