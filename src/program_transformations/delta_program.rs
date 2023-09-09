use datalog_syntax::Program;
use crate::helpers::helpers::deltaify_atom;

pub fn make_delta_program(program: &Program, update: bool) -> Program {
    let idb_relation_symbols: Vec<_> = program.inner.iter().map(|rule| &rule.head.symbol).collect();

    let mut delta_program = vec![];
    program.inner.iter().for_each(|rule| {
        let mut new_rule = rule.clone();
        deltaify_atom(&mut new_rule.head);
        if !rule.body.iter().any(|body_atom| {
            idb_relation_symbols
                .iter()
                .any(|idb_relation_symbol| *idb_relation_symbol == &body_atom.symbol)
        }) && !update {
            delta_program.push(new_rule);
        } else {
            new_rule
                .body
                .iter()
                .enumerate()
                .for_each(|(inner_atom_id, body_atom)| {
                    if update
                        || idb_relation_symbols
                        .iter()
                        .any(|idb_relation| *idb_relation == &body_atom.symbol)
                    {
                        let mut new_inner_rule = new_rule.clone();
                        deltaify_atom(&mut new_inner_rule.body[inner_atom_id]);

                        delta_program.push(new_inner_rule);
                    }
                });
        }
    });

    delta_program.dedup();

    Program::from(delta_program)
}

#[cfg(test)]
mod test {
    use datalog_syntax::*;
    use datalog_rule_macro::*;
    use crate::program_transformations::delta_program::make_delta_program;

    #[test]
    fn test_make_sne_program_nonlinear_update() {
        let program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)] };

        let actual_program = make_delta_program(&program, true);
        let expected_program = program! {
            Δtc(?x, ?y) <- [Δe(?x, ?y)],
            Δtc(?x, ?z) <- [Δtc(?x, ?y), tc(?y, ?z)],
            Δtc(?x, ?z) <- [tc(?x, ?y), Δtc(?y, ?z)],
        };

        assert_eq!(expected_program, actual_program)
    }

    #[test]
    fn test_make_sne_program_nonlinear_initial() {
        let program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)],
        };

        let actual_program = make_delta_program(&program, false);
        let expected_program = program! {
            Δtc(?x, ?y) <- [e(?x, ?y)],
            Δtc(? x, ?z) <- [Δtc(? x, ?y), tc(? y, ?z)],
            Δtc(? x, ?z) <-[tc(? x, ?y), Δtc(? y, ?z)],
        };

        assert_eq!(expected_program, actual_program)
    }

    #[test]
    fn test_make_sne_program_linear_initial() {
        let program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)],
        };

        let actual_program = make_delta_program(&program, false);
        let expected_program = program! {
            Δtc(?x, ?y) <- [e(?x, ?y)],
            Δtc(?x, ?z) <- [e(?x, ?y), Δtc(?y, ?z)],
        };

        assert_eq!(expected_program, actual_program)
    }

    #[test]
    fn test_make_sne_program_linear_update() {
        let program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)],
        };

        let actual_program = make_delta_program(&program, true);
        let expected_program = program! {
            Δtc(?x, ?y) <- [Δe(?x, ?y)],
            Δtc(?x, ?z) <- [Δe(?x, ?y), tc(?y, ?z)],
            Δtc(?x, ?z) <- [e(?x, ?y), Δtc(?y, ?z)],
        };

        assert_eq!(expected_program, actual_program)
    }
}