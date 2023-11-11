use ascent::ascent;
use chibi_datalog::engine::datalog::ChibiRuntime;
use crepe::crepe;
use datalog_rule_macro::program;
use datalog_syntax::*;
use std::time::Instant;

crepe! {
    @input
    struct e(usize, usize);

    @output
    struct tc(usize, usize);

    tc(x, y) <- e(x, y);
    tc(x, z) <- e(x, y), tc(y, z);
}

ascent! {
    relation e(usize, usize);
    relation tc(usize, usize);

    tc(x, y) <-- e(x, y);
    tc(x, z) <-- e(x, y), tc(y, z);
}

fn main() {
    let program = program! {
        tc(?x, ?y) <- [e(?x, ?y)],
        tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
    };

    let mut chibi_runtime = ChibiRuntime::new(program);
    let mut ascnt_runtime = AscentProgram::default();
    let mut crepe_runtime = Crepe::new();

    let data = include_str!("../data/graph.txt");
    data.lines().into_iter().for_each(|line| {
        let triple: Vec<_> = line.split(" ").collect();
        let from: usize = triple[0].parse().unwrap();
        let to: usize = triple[1].parse().unwrap();

        chibi_runtime.insert("e", vec![from.into(), to.into()]);
        crepe_runtime.e.push(e(from, to));
        ascnt_runtime.e.push((from, to));
    });

    let now = Instant::now();
    chibi_runtime.poll();
    println!("chibi: {}", now.elapsed().as_micros());

    let now = Instant::now();
    crepe_runtime.run();
    println!("crepe: {}", now.elapsed().as_micros());

    let now = Instant::now();
    ascnt_runtime.run();
    println!("ascent: {}", now.elapsed().as_micros());
}
