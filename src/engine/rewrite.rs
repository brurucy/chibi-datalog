use ahash::{HashMap, HashSet};
use datalog_syntax::{AnonymousGroundAtom, Atom, Rule, Term, TypedValue};

#[derive(Ord, PartialOrd, Eq, PartialEq, Clone, Hash)]
pub enum InternedTerm {
    Variable(usize),
    Constant(TypedValue),
}

#[derive(Ord, PartialOrd, Eq, PartialEq, Clone, Hash)]
pub struct InternedAtom {
    pub terms: Vec<InternedTerm>,
    pub symbol: usize,
}

#[derive(Ord, PartialOrd, Eq, PartialEq, Clone, Hash)]
pub struct InternedRule {
    pub head: InternedAtom,
    pub body: Vec<InternedAtom>,
}

pub fn intern_atom<'a>(atom: Atom, relation_to_id: &HashMap<String, usize>) -> InternedAtom {
    let interned_symbol = relation_to_id.get(&atom.symbol).unwrap();
    let interned_terms = atom
        .terms
        .into_iter()
        .map(|term| match term {
            Term::Variable(variable_name) => {
                InternedTerm::Variable(*relation_to_id.get(&variable_name).unwrap())
            }
            Term::Constant(constant) => InternedTerm::Constant(constant),
        })
        .collect();

    return InternedAtom {
        symbol: *interned_symbol,
        terms: interned_terms,
    };
}

pub fn intern_rule(rule: Rule) -> (InternedRule, HashMap<usize, String>) {
    let symbols: HashSet<String> = vec![rule.head.symbol.clone()]
        .into_iter()
        .chain(rule.body.clone().into_iter().map(|atom| atom.symbol))
        .collect();

    let variable_names: HashSet<String> = vec![rule.clone().head.terms]
        .into_iter()
        .chain(rule.body.clone().into_iter().map(|atom| atom.terms))
        .flat_map(|terms| terms)
        .filter_map(|term| match term {
            Term::Variable(name) => Some(name),
            Term::Constant(_) => None,
        })
        .collect();

    let all_names: Vec<_> = symbols.union(&variable_names).cloned().collect();
    let id_to_relation: HashMap<usize, String> = all_names.into_iter().enumerate().collect();
    let relation_to_id: HashMap<String, usize> = id_to_relation
        .clone()
        .into_iter()
        .map(|(idx, relation)| (relation, idx))
        .collect();

    return (
        InternedRule {
            head: intern_atom(rule.head, &relation_to_id),
            body: rule
                .body
                .into_iter()
                .map(|atom| intern_atom(atom, &relation_to_id))
                .collect(),
        },
        id_to_relation,
    );
}

pub type Domain = usize;
pub type Substitution = (Domain, TypedValue);

#[derive(Clone, Debug, PartialEq, PartialOrd, Eq, Ord, Hash, Default)]
pub struct Rewrite {
    pub inner: Vec<Substitution>,
}

impl Rewrite {
    pub fn get(&self, key: Domain) -> Option<&TypedValue> {
        for sub in &self.inner {
            if sub.0 == key {
                return Some(&sub.1);
            }
        }

        None
    }
    pub fn insert(&mut self, value: Substitution) {
        if self.get(value.0).is_none() {
            self.inner.push(value)
        }
    }
    pub fn len(&self) -> usize {
        self.inner.len()
    }
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
    pub fn extend(&mut self, other: Self) {
        other.inner.into_iter().for_each(|sub| {
            self.insert(sub);
        })
    }
    pub fn apply(&self, atom: &InternedAtom) -> InternedAtom {
        return InternedAtom {
            terms: atom
                .terms
                .iter()
                .map(|term| {
                    if let InternedTerm::Variable(identifier) = term {
                        if let Some(constant) = self.get(*identifier) {
                            return InternedTerm::Constant(constant.clone());
                        }
                    }

                    term.clone()
                })
                .collect(),
            symbol: atom.symbol,
        };
    }
    pub fn remove(&mut self, key: Domain) -> TypedValue {
        let position = self.inner.iter().position(|value| value.0 == key).unwrap();

        return self.inner.swap_remove(position).1;
    }
    pub fn ground(mut self, atom: &InternedAtom) -> AnonymousGroundAtom {
        atom.terms
            .iter()
            .map(|term| {
                return match term {
                    InternedTerm::Variable(inner) => self.remove(*inner),
                    InternedTerm::Constant(inner) => inner.clone(),
                };
            })
            .collect()
    }
}

pub fn unify(left: &InternedAtom, right: &AnonymousGroundAtom) -> Option<Rewrite> {
    // If atoms don't have the same term length, they can't be unified
    if left.terms.len() != right.len() {
        return None;
    }

    let mut rewrite: Rewrite = Default::default();

    for (left_term, right_term) in left.terms.iter().zip(right.iter()) {
        match left_term {
            // If both terms are constants and they don't match, unification fails
            InternedTerm::Constant(l_const) if l_const != right_term => return None,
            // If left term is a variable, substitute it with the right constant
            InternedTerm::Variable(l_var) => {
                // If this variable was already assigned a different constant, unification fails
                if let Some(existing_const) = rewrite.get(*l_var) {
                    if existing_const != right_term {
                        return None;
                    }
                } else {
                    rewrite.insert((*l_var, right_term.clone()));
                }
            }
            _ => {}
        }
    }

    Some(rewrite)
}
