use crate::engine::rewrite::{unify, Rewrite};
use crate::engine::storage::RelationStorage;
use datalog_syntax::{AnonymousGroundAtom, Atom, Rule, Term, TypedValue};
use std::collections::{HashMap, HashSet};
use std::time::Instant;

pub struct RuleEvaluator<'a> {
    rule: &'a Rule,
    facts_storage: &'a RelationStorage,
}

impl<'a> RuleEvaluator<'a> {
    pub(crate) fn new(facts_storage: &'a RelationStorage, rule: &'a Rule) -> Self {
        Self {
            rule,
            facts_storage,
        }
    }
}

pub fn unique_column_combinations(
    rule: &Rule,
) -> (HashMap<String, Vec<Vec<usize>>>, Vec<Vec<usize>>) {
    let mut out: HashMap<String, Vec<Vec<usize>>> = Default::default();
    let mut join_key_sequence = vec![];
    let mut variables: HashSet<String> = HashSet::new();

    for body_atom in &rule.body {
        let indices: Vec<_> = body_atom
            .terms
            .iter()
            .enumerate()
            .filter_map(|(idx, term)| match term {
                Term::Variable(var) if !variables.contains(var) => {
                    variables.insert(var.clone());
                    None
                }
                Term::Variable(_) => Some(idx),
                Term::Constant(_) => Some(idx),
            })
            .collect();

        join_key_sequence.push(indices.clone());
        let entry = out.entry(body_atom.symbol.clone()).or_default();
        entry.push(indices);
    }

    (out, join_key_sequence)
}

pub type MaskedAtom<'a> = Vec<Option<&'a TypedValue>>;

fn mask_atom(atom: &Atom) -> MaskedAtom {
    let mut masked_atom = Vec::new();

    atom.terms
        .iter()
        .map(|term| match term {
            Term::Constant(value) => Some(value),
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

impl<'a> RuleEvaluator<'a> {
    // Doing it depth-first might warrant better results with iterators, since computation
    // would emit facts faster than breadth-first (which defers until all of them are ready to be
    // emitted)
    pub fn step(&self) -> impl Iterator<Item = AnonymousGroundAtom> + 'a {
        let (uccs, join_key_sequence) = unique_column_combinations(self.rule);
        let index1 = index(&uccs, &self.facts_storage);

        let mut current_rewrites: Vec<Rewrite> = vec![Rewrite::default()];

        for (current_body_atom, join_key) in
            self.rule.body.iter().zip(join_key_sequence.into_iter())
        {
            let current_unification_targets: Vec<_> = current_rewrites
                .clone()
                .into_iter()
                .map(|rewrite| (rewrite.apply(current_body_atom), rewrite))
                .collect();

            let current_masked_unification_targets: Vec<_> = current_unification_targets
                .iter()
                .map(|(current_furthered_body_atom, rewrite)| {
                    (
                        mask_atom(current_furthered_body_atom),
                        current_furthered_body_atom,
                        rewrite,
                    )
                })
                .collect();

            let matches_by_symbol = index1.get(&current_body_atom.symbol).unwrap();
            let matches_by_positions = matches_by_symbol.get(&join_key).unwrap();

            current_rewrites.clear();
            current_masked_unification_targets.into_iter().for_each(
                |(masked_atom, unification_target, rewrite)| {
                    if let Some(matches_by_mask) = matches_by_positions.get(&masked_atom) {
                        matches_by_mask.iter().for_each(|current_ground_atom| {
                            if let Some(new_rewrite) =
                                unify(unification_target, current_ground_atom)
                            {
                                let mut local_rewrite = rewrite.clone();
                                local_rewrite.extend(new_rewrite);

                                current_rewrites.push(local_rewrite);
                            };
                        });
                    }
                },
            );
        }

        current_rewrites
            .into_iter()
            .map(|rewrite| rewrite.ground(self.rule.head.clone()))
    }
}

#[cfg(test)]
mod tests {
    use crate::evaluation::rule::unique_column_combinations;
    use datalog_rule_macro::rule;
    use datalog_syntax::*;
    use std::collections::HashMap;

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
    }

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
