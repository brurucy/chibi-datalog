use datalog_syntax::{Atom, Program};

pub const DELTA_PREFIX: &str = "Δ";
fn deltaify_atom(atom: &mut Atom) {
    atom.symbol = format!("{}{}", DELTA_PREFIX, atom.symbol)
}

fn make_delta_program(program: &Program) -> Program {
    let delta_program: Vec<_> = program
        .inner
        .iter()
        .flat_map(|rule| {
            let mut new_rule = rule.clone();
            deltaify_atom(&mut new_rule.head);

            new_rule
                .body
                .iter()
                .enumerate()
                .map(|(inner_atom_id, inner_atom)| {
                    let mut new_inner_rule = new_rule.clone();
                    deltaify_atom(&mut new_inner_rule.body[inner_atom_id]);

                    new_inner_rule
                })
                .collect::<Vec<_>>()
        })
        .collect();

    Program::from(delta_program)
}

#[cfg(test)]
mod tests {
    use crate::helpers::program_transformations::make_delta_program;
    use datalog_rule_macro::rule;
    use datalog_syntax::*;

    #[test]
    fn test_make_sne_program_nonlinear() {
        let program = Program::from(vec![
            rule! { tc(?x, ?y) <- [e(?x, ?y)] },
            rule! { tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)] },
        ]);

        let actual_program = make_delta_program(&program);
        let expected_program = Program::from(vec![
            rule! { Δtc(?x, ?y) <- [Δe(?x, ?y)]},
            rule! { Δtc(?x, ?z) <- [Δtc(?x, ?y), tc(?y, ?z)]},
            rule! { Δtc(?x, ?z) <- [tc(?x, ?y), Δtc(?y, ?z)]},
        ]);

        assert_eq!(expected_program, actual_program)
    }

    #[test]
    fn test_make_sne_program_linear() {
        let program = Program::from(vec![
            rule! { tc(?x, ?y) <- [e(?x, ?y)] },
            rule! { tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)] },
        ]);

        let actual_program = make_delta_program(&program);
        let expected_program = Program::from(vec![
            rule! { Δtc(?x, ?y) <- [Δe(?x, ?y)]},
            rule! { Δtc(?x, ?z) <- [Δe(?x, ?y), tc(?y, ?z)]},
            rule! { Δtc(?x, ?z) <- [e(?x, ?y), Δtc(?y, ?z)]},
        ]);

        assert_eq!(expected_program, actual_program)
    }
}
