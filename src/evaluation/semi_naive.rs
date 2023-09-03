use datalog_syntax::{ Program };
use crate::engine::storage::RelationStorage;
use crate::evaluation::rule::RuleEvaluator;
use crate::helpers::program_transformations::DELTA_PREFIX;

fn semi_naive_evaluation(fact_storage: &mut RelationStorage, program: &Program) {
    // Ensure that all indexes are in place
    program
        .inner
        .iter()
        .for_each(|rule| {
            if rule.head.symbol.contains(DELTA_PREFIX) {
                fact_storage
                    .inner
                    .entry(rule.head.symbol.clone())
                    .or_default();
            }
        });
    // Evaluate
    loop {
        let rule_applications = program
            .inner
            .iter()
            .map(|rule| (&rule.head.symbol, RuleEvaluator::new(fact_storage, rule)))
            .collect();


    }
}
