use ahash::{HashMap, HashSet};
use datalog_syntax::{Program, Term};

pub fn compute_unique_column_combinations_and_join_order(
    programs: Vec<&Program>,
) -> (
    HashMap<String, Vec<Vec<usize>>>,
    HashMap<usize, HashMap<usize, Vec<Vec<usize>>>>,
) {
    let mut out: HashMap<String, Vec<Vec<usize>>> = Default::default();
    let mut join_key_sequence: HashMap<usize, HashMap<usize, Vec<Vec<usize>>>> = Default::default();
    let mut variables: HashSet<String> = Default::default();

    for ((program_id, program)) in programs.iter().enumerate() {
        let mut program_join_key_sequence: HashMap<usize, Vec<Vec<usize>>> = Default::default();
        for rule in &program.inner {
            let mut rule_join_key_sequence = vec![];
            for body_atom in &rule.body {
                let indices: Vec<_> = body_atom
                    .terms
                    .iter()
                    .enumerate()
                    .filter_map(|(idx, term)| match term {
                        Term::Variable(var) if !variables.contains(&var) => {
                            variables.insert(var.clone());
                            None
                        }
                        Term::Variable(_) => Some(idx),
                        Term::Constant(_) => Some(idx),
                    })
                    .collect();

                let entry = out.entry(body_atom.symbol.clone()).or_default();
                entry.push(indices.clone());

                rule_join_key_sequence.push(indices);
            }

            program_join_key_sequence.insert(rule.id, rule_join_key_sequence);
        }

        join_key_sequence.insert(program_id, program_join_key_sequence);
    }

    (out, join_key_sequence)
}

pub struct ProgramIndex {
    pub unique_program_column_combinations: HashMap<String, Vec<Vec<usize>>>,
    pub binding_guided_join_order: HashMap<usize, HashMap<usize, Vec<Vec<usize>>>>,
}

impl From<Vec<&Program>> for ProgramIndex {
    fn from(value: Vec<&Program>) -> Self {
        let index_inner = compute_unique_column_combinations_and_join_order(value);

        return Self {
            unique_program_column_combinations: index_inner.0,
            binding_guided_join_order: index_inner.1,
        };
    }
}
