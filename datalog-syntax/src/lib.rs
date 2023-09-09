use ordered_float::OrderedFloat;

#[derive(Eq, Ord, PartialEq, PartialOrd, Clone, Debug, Hash)]
pub enum TypedValue {
    Str(String),
    Int(usize),
    Bool(bool),
    Float(OrderedFloat<f64>),
}

impl From<String> for TypedValue {
    fn from(value: String) -> Self {
        TypedValue::Str(value)
    }
}

impl From<&str> for TypedValue {
    fn from(value: &str) -> Self {
        TypedValue::Str(value.to_string())
    }
}

impl From<usize> for TypedValue {
    fn from(value: usize) -> Self {
        TypedValue::Int(value)
    }
}

impl From<bool> for TypedValue {
    fn from(value: bool) -> Self {
        TypedValue::Bool(value)
    }
}

impl From<f64> for TypedValue {
    fn from(value: f64) -> Self {
        TypedValue::Float(OrderedFloat::from(value))
    }
}

pub type Variable = String;

#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Clone)]
pub enum Term {
    Variable(String),
    Constant(TypedValue),
}

pub type AnonymousGroundAtom = Vec<TypedValue>;

#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Clone)]
pub struct Atom {
    pub terms: Vec<Term>,
    pub symbol: String,
}

pub enum Matcher {
    Any,
    Constant(TypedValue)
}

pub struct Query<'a> {
    pub matchers: Vec<Matcher>,
    pub symbol: &'a str
}

pub struct QueryBuilder<'a> {
    query: Query<'a>
}

impl<'a> QueryBuilder<'a> {
    fn new(relation: &'a str) -> Self {
        QueryBuilder {
            query: Query {
                matchers: vec![],
                symbol: relation
            }
        }
    }
    fn with_any(&mut self) {
        self.query.matchers.push(Matcher::Any)
    }
    fn with_constant(&mut self, value: TypedValue) {
        self.query.matchers.push(Matcher::Constant(value))
    }
}

impl<'a> From<QueryBuilder<'a>> for Query<'a> {
    fn from(value: QueryBuilder<'a>) -> Self {
        value.query
    }
}

#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Clone)]
pub struct Rule {
    pub head: Atom,
    pub body: Vec<Atom>,
}

#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Clone)]
pub struct Program {
    pub inner: Vec<Rule>,
}

impl From<Vec<Rule>> for Program {
    fn from(value: Vec<Rule>) -> Self {
        Self { inner: value }
    }
}
