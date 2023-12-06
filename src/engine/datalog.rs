use crate::engine::rewrite::{reliably_intern_rule, unify, InternedTerm, Rewrite};
use crate::engine::storage::RelationStorage;
use crate::evaluation::query::pattern_match;
use crate::interning::fact_registry::Row;
use ahash::AHasher;
use dashmap::DashMap;
use datalog_syntax::*;
use dbsp::operator::FilterMap;
use dbsp::{
    CollectionHandle, DBSPHandle, IndexedZSet, OrdIndexedZSet, OutputHandle, Runtime, Stream,
};
use lasso::{Key, Rodeo, Spur};
use lazy_static::lazy_static;
use std::collections::HashSet;
use std::fmt;
use std::hash::{Hash, Hasher};

lazy_static! {
    static ref FACT_REGISTRY: DashMap<usize, Vec<TypedValue>> = DashMap::new();
}

pub type FlattenedInternedFact = (usize, Vec<TypedValue>);
pub type FlattenedInternedAtom = (usize, Vec<InternedTerm>);
pub type FlattenedInternedRule = (usize, FlattenedInternedAtom, Vec<FlattenedInternedAtom>);

pub type Weight = isize;
pub struct ChibiRuntime {
    interner: Rodeo,
    dbsp_runtime: DBSPHandle,
    fact_sink: CollectionHandle<FlattenedInternedFact, Weight>,
    rule_sink: CollectionHandle<FlattenedInternedRule, Weight>,
    fact_source: OutputHandle<OrdIndexedZSet<usize, Vec<TypedValue>, Weight>>,
    materialisation: RelationStorage,
    safe: bool,
}

fn hashisher<T: Hash>(key: &[T]) -> Row {
    let mut hasher = AHasher::default();

    key.iter()
        .for_each(|masked_value| masked_value.hash(&mut hasher));

    Row(hasher.finish())
}

pub fn compute_unique_column_sets(rule: &FlattenedInternedRule) -> Vec<(usize, Vec<usize>)> {
    let mut out = vec![];
    let mut variables: HashSet<usize> = Default::default();
    let mut fresh_variables: HashSet<usize> = Default::default();
    for body_atom in &rule.2 {
        let index: Vec<_> = body_atom
            .1
            .iter()
            .enumerate()
            .flat_map(|(idx, term)| match term {
                InternedTerm::Variable(inner) => {
                    if !variables.contains(inner) {
                        fresh_variables.insert(*inner);
                        None
                    } else {
                        Some(idx)
                    }
                }
                InternedTerm::Constant(_) => Some(idx),
            })
            .collect();
        variables.extend(fresh_variables.iter());
        out.push((body_atom.0, index));

        fresh_variables.clear();
    }

    return out;
}

// tc(?x, ?z) <- e(?x, ?y), tc(?y, ?z)
// [(e, (tc, [1, 0]))]
// T(?z, 0, ?y) <- T(?x, 1, ?y), T(?z, 0, ?x),
// [(t, (t, [2, 1, 0])]

struct SliceDisplay<'a, T: 'a>(&'a [T]);

impl<'a, T: fmt::Debug + 'a> fmt::Debug for SliceDisplay<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut first = true;
        for item in self.0 {
            if !first {
                write!(f, ", {:?}", item)?;
            } else {
                write!(f, "{:?}", item)?;
            }
            first = false;
        }
        Ok(())
    }
}

fn is_ground(atom: &Vec<InternedTerm>) -> bool {
    return !atom.iter().any(|term| match term {
        InternedTerm::Variable(_) => true,
        InternedTerm::Constant(_) => false,
    });
}

impl ChibiRuntime {
    pub fn insert(&mut self, relation: &str, ground_atom: AnonymousGroundAtom) -> bool {
        let interned_symbol = self.interner.get_or_intern(relation);

        self.fact_sink
            .push((interned_symbol.into_usize(), ground_atom.clone()), 1);

        self.safe = false;

        self.materialisation.insert(relation, ground_atom)
    }
    pub fn remove(&mut self, query: &Query) -> impl Iterator<Item = AnonymousGroundAtom> {
        let mut removals = vec![];
        let query_symbol = query.symbol;
        let interned_symbol = self.interner.get(query_symbol).unwrap();

        let removal_targets: Vec<_> = self
            .materialisation
            .get_relation(query_symbol)
            .iter()
            .filter(|row| pattern_match(query, self.materialisation.fact_registry.get(**row)))
            .cloned()
            .collect();

        removal_targets.iter().for_each(|&candidate| {
            self.fact_sink.push(
                (
                    interned_symbol.into_usize(),
                    self.materialisation.fact_registry.get(candidate).clone(),
                ),
                -1,
            );
        });

        self.safe = false;

        let mut relation = self.materialisation.inner.get_mut(query_symbol).unwrap();
        removal_targets.iter().for_each(|candidate| {
            relation.remove(candidate);
        });

        removal_targets.into_iter().for_each(|candidate| {
            removals.push(self.materialisation.fact_registry.remove(candidate))
        });

        removals.into_iter()
    }
    pub fn contains(
        &self,
        relation: &str,
        ground_atom: &AnonymousGroundAtom,
    ) -> Result<bool, String> {
        if !self.safe() {
            return Err("poll needed to obtain correct results".to_string());
        }

        Ok(self.materialisation.contains(relation, ground_atom))
    }
    pub fn query<'a>(
        &'a self,
        query: &'a Query,
    ) -> Result<impl Iterator<Item = &AnonymousGroundAtom> + 'a, String> {
        if !self.safe() {
            return Err("poll needed to obtain correct results".to_string());
        }
        return Ok(self
            .materialisation
            .get_relation(query.symbol)
            .iter()
            .map(|fact| self.materialisation.fact_registry.get(*fact))
            .filter(|fact| pattern_match(query, fact)));
    }
    pub fn poll(&mut self) {
        self.dbsp_runtime.step().unwrap();

        let consolidated = self.fact_source.consolidate();
        consolidated
            .iter()
            .for_each(|(relation_identifier, fresh_fact, weight)| {
                let spur = Spur::try_from_usize(relation_identifier).unwrap();
                let sym = self.interner.resolve(&spur);
                //println!("{} - {}({:?})", weight, sym, SliceDisplay(&fresh_fact));

                if weight.signum() > 0 {
                    self.materialisation.insert(sym, fresh_fact);
                } else {
                    self.materialisation.remove(sym, fresh_fact);
                }
            });

        self.dbsp_runtime.dump_profile("./prof").unwrap();

        self.safe = true;
    }

    pub fn new(program: Program) -> Self {
        let mut materialisation: RelationStorage = Default::default();
        let mut relations = HashSet::new();

        let mut interner: Rodeo<Spur> = Rodeo::new();
        let (mut dbsp_runtime, ((fact_source, fact_sink), rule_sink)) =
            Runtime::init_circuit(8, |circuit| {
                let (rule_source, rule_sink) =
                    circuit.add_input_zset::<FlattenedInternedRule, Weight>();
                let (fact_source, fact_sink) =
                    circuit.add_input_zset::<FlattenedInternedFact, Weight>();

                let facts_by_symbol = fact_source
                    .index_with(move |(symbol, fact)| {
                        let fact_hash = FACT_REGISTRY.hash_usize(fact);
                        FACT_REGISTRY.insert(fact_hash, fact.clone());

                        (*symbol, fact_hash)
                    });

                // tc(?x, ?z) <- e(?x, ?y), tc(?y, ?z)
                // --   cartesian stupid way   - indexes by symbol
                // ---- e, tc
                // --   demand-driven indexing - indexes by symbol, unique column combination, values, matches
                // ---- e : [], tc: [0 : [ ... ]]
                // --   relational datalog     - indexes by symbol, join key
                // ---- e : (tc, [1, 0]), tc: []
                // --   index_with(e, [1, 0]) >< filter(facts, tc)
                let unique_column_sets = rule_source.flat_map_index(compute_unique_column_sets);

                // (relation_symbol, terms) <- (relation_symbol, terms)
                let fact_index = facts_by_symbol
                    .join_index(&unique_column_sets, |relation_symbol, fact_registration, column_set| {
                        let fact = FACT_REGISTRY.get(fact_registration).unwrap();

                        let mut projected_fact = vec![None; fact.len()];
                        if !(column_set.len() == 0) {
                            column_set.iter().for_each(|column| {
                                projected_fact[*column] = Some(fact[*column].clone())
                            });
                        }

                        Some(((*relation_symbol, hashisher(&projected_fact)), *fact_registration))
                    });

                // (rule_id, (head, body)) <- (rule_id, head, body)
                let rules_by_id =
                    rule_source.index_with(|(id, head, body)| (*id, (head.clone(), body.clone())));

                // ((rule_id, atom_id), atom) -- this is what will "guide" iteration.
                let iteration = rules_by_id.flat_map_index(|(rule_id, (_head, body))| {
                    body.iter()
                        .enumerate()
                        .map(move |(atom_position, atom)| ((*rule_id, atom_position), atom.clone()))
                        .collect::<Vec<_>>()
                });

                // ((rule_id, body_size), head_atom) -- this will ensure that only atoms that have been
                // propagated through the whole body will be considered for grounding
                let end_for_grounding = rule_source.index_with(|(id, head, body)| ((*id, body.len()), head.clone()));

                // ((rule_id, 0), empty substitution) -- this signals the start of the computation
                let start = rule_source.index_with(|(rule_id, _head, _body)| ((*rule_id, 0), Rewrite::default()));

                let (inferences, _, _) = circuit
                    .recursive(
                        |child,
                        (idb, idb_index, rewrites): (
                             Stream<_, OrdIndexedZSet<usize, usize, isize>>,
                             Stream<_, OrdIndexedZSet<(usize, Row), usize, isize>>,
                             Stream<_, OrdIndexedZSet<(usize, usize), Rewrite, isize>>,
                        )| {
                            let iteration = iteration.delta0(child);
                            let edb_index = fact_index.delta0(child);
                            let start = start.delta0(child);
                            let end_for_grounding = end_for_grounding.delta0(child);
                            let unique_column_sets = unique_column_sets.delta0(child);
                            let edb = facts_by_symbol.delta0(child);

                            let current_rewrites = rewrites.join_index(
                                &iteration,
                                |key, rewrite, current_body_atom| {
                                    let fresh_atom = rewrite.apply(current_body_atom.1.clone());

                                    let mut mask = vec![None; fresh_atom.len()];
                                    fresh_atom.iter().enumerate().for_each(|(idx,term)| {
                                        match term {
                                            InternedTerm::Constant(inner) => {
                                                mask[idx] = Some(inner.clone())
                                            },
                                            _ => {}
                                        }
                                    });


                                    if !is_ground(&fresh_atom) {
                                        return Some((
                                            (current_body_atom.0, hashisher(&mask)),
                                            (*key, fresh_atom, rewrite.clone()),
                                        ));
                                    }

                                    return None;
                                },
                            );

                            let cartesian_product =
                                idb_index.join_index(&current_rewrites, |(_relation_symbol, _projection), fact_registration, ((rule_id, atom_position), fresh_atom, rewrite)| {
                                    let fact = FACT_REGISTRY.get(fact_registration).unwrap();

                                    if let Some(unification) = unify(fresh_atom, &fact) {
                                        let mut extended_sub = rewrite.clone();
                                        extended_sub.extend(unification);

                                        return Some(((*rule_id, atom_position + 1), extended_sub))
                                    };

                                    return None;
                                });

                            let fresh_facts = end_for_grounding
                                .join_index(&cartesian_product, |(_rule_id, _final_atom_position), (head_atom_symbol, head_atom), final_substitution| {
                                    let fresh_fact = final_substitution.clone().ground(head_atom.clone());
                                    let fresh_fact_registration = FACT_REGISTRY.hash_usize(&fresh_fact);
                                    FACT_REGISTRY.insert(fresh_fact_registration, fresh_fact);

                                    Some((*head_atom_symbol, fresh_fact_registration))
                                });


                            let fresh_projections = fresh_facts
                                .join_index(&unique_column_sets, |relation_symbol, fact_registration, column_set| {
                                    let fact = FACT_REGISTRY.get(fact_registration).unwrap();

                                    let mut projected_fact = vec![None; fact.len()];
                                    if !(column_set.len() == 0) {
                                        column_set.iter().for_each(|column| {
                                            projected_fact[*column] = Some(fact[*column].clone())
                                        });
                                    }

                                    Some(((*relation_symbol, hashisher(&projected_fact)), *fact_registration))
                                });

                            Ok((edb.plus(&fresh_facts), edb_index.plus(&fresh_projections), start.plus(&cartesian_product)))
                        },
                    )
                    .unwrap();

                let inferences = inferences.map_index(|(key, value)| (*key, FACT_REGISTRY.get(value).unwrap().clone()));

                Ok((((inferences.output()), fact_sink), rule_sink))
            })
            .unwrap();

        program.inner.iter().for_each(|rule| {
            relations.insert(&rule.head.symbol);

            rule.body.iter().for_each(|body_atom| {
                relations.insert(&body_atom.symbol);
            });

            let interned_rule = reliably_intern_rule(rule.clone(), &mut interner);
            let flattened_head = (interned_rule.head.symbol, interned_rule.head.terms);
            let flattened_body = interned_rule
                .body
                .into_iter()
                .map(|atom| (atom.symbol, atom.terms))
                .collect();

            rule_sink.push((rule.id, flattened_head, flattened_body), 1);
        });

        relations.iter().for_each(|relation_symbol| {
            materialisation
                .inner
                .entry(relation_symbol.to_string())
                .or_default();
        });

        dbsp_runtime.enable_cpu_profiler().unwrap();

        Self {
            interner,
            dbsp_runtime,
            fact_source,
            fact_sink,
            rule_sink,
            materialisation,
            safe: true,
        }
    }
    pub fn safe(&self) -> bool {
        self.safe
    }
}

#[cfg(test)]
mod tests {
    use crate::engine::datalog::ChibiRuntime;
    use datalog_rule_macro::program;
    use datalog_syntax::*;
    use std::collections::HashSet;

    #[test]
    fn integration_test_insertions_only() {
        let tc_program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)],
        };

        let mut runtime = ChibiRuntime::new(tc_program);
        vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
        ]
        .into_iter()
        .for_each(|edge| {
            runtime.insert("e", edge);
        });

        runtime.poll();

        // This query reads as: "Get all in tc with any values in any positions"
        let all = build_query!(tc(_, _));
        // And this one as: "Get all in tc with the first term being a"
        // There also is a QueryBuilder, if you do not want to use a macro.
        let all_from_a = build_query!(tc("a", _));

        let actual_all: HashSet<AnonymousGroundAtom> =
            runtime.query(&all).unwrap().cloned().collect();
        let expected_all: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
            // Second iter
            vec!["a".into(), "c".into()],
            vec!["b".into(), "d".into()],
            // Third iter
            vec!["a".into(), "d".into()],
        ]
        .into_iter()
        .collect();
        assert_eq!(expected_all, actual_all);

        let actual_all_from_a: HashSet<AnonymousGroundAtom> =
            runtime.query(&all_from_a).unwrap().cloned().collect();
        let expected_all_from_a: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["a".into(), "c".into()],
            vec!["a".into(), "d".into()],
        ]
        .into_iter()
        .collect();
        assert_eq!(expected_all_from_a, actual_all_from_a);

        expected_all.iter().for_each(|fact| {
            assert!(runtime.contains("tc", fact).unwrap());
        });

        expected_all_from_a.iter().for_each(|fact| {
            assert!(runtime.contains("tc", fact).unwrap());
        });

        // Update
        runtime.insert("e", vec!["d".into(), "e".into()]);
        assert!(!runtime.safe());
        runtime.poll();
        assert!(runtime.safe());

        let actual_all_after_update: HashSet<AnonymousGroundAtom> =
            runtime.query(&all).unwrap().cloned().collect();
        let expected_all_after_update: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
            // Second iter
            vec!["a".into(), "c".into()],
            vec!["b".into(), "d".into()],
            // Third iter
            vec!["a".into(), "d".into()],
            // Update
            vec!["d".into(), "e".into()],
            vec!["c".into(), "e".into()],
            vec!["b".into(), "e".into()],
            vec!["a".into(), "e".into()],
        ]
        .into_iter()
        .collect();
        assert_eq!(expected_all_after_update, actual_all_after_update);

        let actual_all_from_a_after_update: HashSet<AnonymousGroundAtom> = runtime
            .query(&all_from_a)
            .unwrap()
            .into_iter()
            .cloned()
            .collect();
        let expected_all_from_a_after_update: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["a".into(), "c".into()],
            vec!["a".into(), "d".into()],
            vec!["a".into(), "e".into()],
        ]
        .into_iter()
        .collect();
        assert_eq!(
            expected_all_from_a_after_update,
            actual_all_from_a_after_update
        );
    }
    #[test]
    fn integration_test_deletions() {
        // Queries. The explanation is in the test above
        let all = build_query!(tc(_, _));
        let all_from_a = build_query!(tc("a", _));

        let tc_program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)],
        };

        let mut runtime = ChibiRuntime::new(tc_program);
        vec![
            vec!["a".into(), "b".into()],
            // this extra atom will help with testing that rederivation works
            vec!["a".into(), "e".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
            vec!["d".into(), "e".into()],
        ]
        .into_iter()
        .for_each(|edge| {
            runtime.insert("e", edge);
        });

        runtime.poll();

        let actual_all: HashSet<AnonymousGroundAtom> =
            runtime.query(&all).unwrap().cloned().collect();
        let expected_all: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["a".into(), "e".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
            // Second iter
            vec!["a".into(), "c".into()],
            vec!["b".into(), "d".into()],
            // Third iter
            vec!["a".into(), "d".into()],
            // Fourth iter
            vec!["d".into(), "e".into()],
            vec!["c".into(), "e".into()],
            vec!["b".into(), "e".into()],
        ]
        .into_iter()
        .collect();
        assert_eq!(expected_all, actual_all);

        let actual_all_from_a: HashSet<_> = runtime
            .query(&all_from_a)
            .unwrap()
            .into_iter()
            .cloned()
            .collect();
        let expected_all_from_a: HashSet<_> = vec![
            vec!["a".into(), "b".into()],
            vec!["a".into(), "c".into()],
            vec!["a".into(), "d".into()],
            vec!["a".into(), "e".into()],
        ]
        .into_iter()
        .collect();
        assert_eq!(expected_all_from_a, actual_all_from_a);

        // Update
        // Point removals are a bit annoying, since they incur creating a query.
        let d_to_e = build_query!(e("d", "e"));
        let deletions: Vec<_> = runtime.remove(&d_to_e).collect();
        assert!(!runtime.safe());
        runtime.poll();
        assert!(runtime.safe());

        let actual_all_after_update: HashSet<AnonymousGroundAtom> =
            runtime.query(&all).unwrap().cloned().collect();
        let expected_all_after_update: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
            // Second iter
            vec!["a".into(), "c".into()],
            vec!["b".into(), "d".into()],
            // Third iter
            vec!["a".into(), "d".into()],
            // This remains
            vec!["a".into(), "e".into()],
        ]
        .into_iter()
        .collect();
        assert_eq!(expected_all_after_update, actual_all_after_update);

        let actual_all_from_a_after_update: HashSet<_> = runtime
            .query(&all_from_a)
            .unwrap()
            .into_iter()
            .cloned()
            .collect();
        let expected_all_from_a_after_update: HashSet<_> = vec![
            vec!["a".into(), "b".into()],
            vec!["a".into(), "c".into()],
            vec!["a".into(), "d".into()],
            vec!["a".into(), "e".into()],
        ]
        .into_iter()
        .collect();
        assert_eq!(
            expected_all_from_a_after_update,
            actual_all_from_a_after_update
        );
    }
}
