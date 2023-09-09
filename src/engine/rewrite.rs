use datalog_syntax::{AnonymousGroundAtom, Atom, Term, TypedValue};

pub type Substitution = (String, TypedValue);

#[derive(Clone, Debug, PartialEq, PartialOrd, Eq, Ord, Hash, Default)]
pub struct Rewrite {
    pub inner: Vec<(String, TypedValue)>,
}

impl Rewrite {
    pub fn get(&self, key: &str) -> Option<&TypedValue> {
        for sub in &self.inner {
            if sub.0 == key {
                return Some(&sub.1);
            }
        }

        None
    }
    pub fn insert(&mut self, value: Substitution) {
        if self.get(&value.0).is_none() {
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
    pub fn apply(&self, atom: &Atom) -> Atom {
        return Atom {
            terms: atom
                .terms
                .iter()
                .map(|term| {
                    if let Term::Variable(identifier) = term {
                        if let Some(constant) = self.get(identifier) {
                            return Term::Constant(constant.clone());
                        }
                    }

                    term.clone()
                })
                .collect(),
            symbol: atom.symbol.clone(),
        };
    }
    pub fn ground(&self, atom: Atom) -> AnonymousGroundAtom {
        atom.terms
            .into_iter()
            .map(|term| {
                return match term {
                    Term::Variable(inner) => self.get(&inner).unwrap().clone(),
                    Term::Constant(inner) => inner,
                };
            })
            .collect()
    }
}

pub fn unify(left: &Atom, right: &AnonymousGroundAtom) -> Option<Rewrite> {
    // If atoms don't have the same term length, they can't be unified
    if left.terms.len() != right.len() {
        return None;
    }

    let mut rewrite: Rewrite = Default::default();

    for (left_term, right_term) in left.terms.iter().zip(right.iter()) {
        match left_term {
            // If both terms are constants and they don't match, unification fails
            Term::Constant(l_const) if l_const != right_term => return None,
            // If left term is a variable, substitute it with the right constant
            Term::Variable(l_var) => {
                // If this variable was already assigned a different constant, unification fails
                if let Some(existing_const) = rewrite.get(l_var) {
                    if existing_const != right_term {
                        return None;
                    }
                } else {
                    rewrite.insert(((l_var).clone(), right_term.clone()));
                }
            }
            _ => {}
        }
    }

    Some(rewrite)
}
