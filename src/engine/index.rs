use crate::engine::rewrite::{InternedAtom, InternedTerm};
use crate::engine::storage::RelationStorage;
use ahash::{HashMap, HashMapExt};
use datalog_syntax::{AnonymousGroundAtom, TypedValue};

pub type UniqueColumnCombinations = HashMap<String, Vec<Vec<usize>>>;
pub type MaskedAtom<'a> = Vec<Option<&'a TypedValue>>;

pub fn mask_atom(atom: &InternedAtom) -> MaskedAtom {
    let mut masked_atom = Vec::new();

    atom.terms
        .iter()
        .map(|term| match term {
            InternedTerm::Constant(value) => Some(value),
            _ => None,
        })
        .for_each(|masked_value| masked_atom.push(masked_value));

    return masked_atom;
}

fn index<'a>(
    unique_column_combinations: &HashMap<String, Vec<Vec<usize>>>,
    facts_by_relation: &'a RelationStorage,
    // What the fuck
) -> HashMap<String, HashMap<Vec<usize>, HashMap<MaskedAtom<'a>, Vec<&'a AnonymousGroundAtom>>>> {
    let mut results: HashMap<
        String,
        HashMap<Vec<usize>, HashMap<MaskedAtom<'a>, Vec<&'a AnonymousGroundAtom>>>,
    > = HashMap::new();

    // Iterate over each unique column combination.
    for (symbol, uccs) in unique_column_combinations.iter() {
        let current_relation_entry = results.entry(symbol.clone()).or_default();
        uccs.iter().for_each(|ucc| {
            let current_ucc_entry = current_relation_entry.entry(ucc.clone()).or_default();

            if let Some(facts) = facts_by_relation.inner.get(symbol) {
                for fact in facts {
                    let mut projected_row = vec![None; fact.len()];

                    // Perform the projection using the unique columns.
                    for &column_index in ucc {
                        if column_index < fact.len() {
                            projected_row[column_index] = Some(&fact[column_index]);
                        }
                    }

                    let current_masked_atoms = current_ucc_entry.entry(projected_row).or_default();
                    current_masked_atoms.push(fact);
                }
            }
        });
    }

    results
}

pub struct Index<'a> {
    pub inner:
        HashMap<String, HashMap<Vec<usize>, HashMap<MaskedAtom<'a>, Vec<&'a AnonymousGroundAtom>>>>,
}

impl<'a> Index<'a> {
    pub fn new(
        relation_storage: &'a RelationStorage,
        uccs: &HashMap<String, Vec<Vec<usize>>>,
    ) -> Self {
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
