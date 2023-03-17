use crate::typing::{Hole, Kind, Pred, Qual};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Span<A>(A, pub std::ops::Range<usize>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Ident(pub &'static str);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DataDecl {
    pub data_name: Ident,
    pub type_names: Vec<Ident>,
    pub constructors: Vec<(Ident, Vec<Ident>)>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DefnDecl<E> {
    Set(Ident, E),                       // (set $name)
    Fun(Ident, Vec<Ident>, E),           // (defn $name)
    Rec(Ident, Vec<Ident>, E),           // (rec defn $name)
    Do(Ident, Vec<Ident>, Vec<Stmt<E>>), // (defn* $name)
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ClassDecl {
    pub class_name: Ident,
    pub type_names: Vec<Ident>,
    pub predicates: Vec<Qual<Pred>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InstDecl<E> {
    pub predicates: Vec<Qual<Ident>>,
    pub functions: im::HashMap<Ident, DefnDecl<E>, fxhash::FxBuildHasher>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Decl<E> {
    Data(DataDecl),
    Class(ClassDecl),
    Defun(DefnDecl<E>),
    Eval(E),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Prim {
    True,
    False,
    Decimal(i128, i128),
    Int(i128),
    String(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Pat {
    Prim(Prim),

    /// constructs
    Atom(Ident), // $name
    At(Ident, Box<Pat>),   // (@ $name $pat)
    Cons(Ident, Vec<Pat>), // ($name $pat*)
    Wild,                  // _
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Exp {
    Prim(Prim),

    // constructs
    Atom(Ident),
    Cons(Box<Exp>, Box<Exp>),
    Nil,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Stmt<E> {
    Binding(Ident, E),
    Eval(E),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    Prim(Prim),

    // expressions
    Nil,
    Atom(Ident),
    Do(Vec<Stmt<Term>>),
    As(Box<Term>, Ident),
    Lam(Ident, Box<Term>),
    App(Box<Term>, Box<Term>),
    Let(Ident, Box<Term>, Box<Term>),
    Match(Box<Term>, Vec<(Pat, Term)>),

    // *internal*
    Closure(Vec<(String, Term)>, Ident, Box<Term>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Elab {
    Prim(Prim),

    // expressions
    Nil,
    Atom(Ident, Vec<Pred>, Hole),             // type(*ident)
    Do(Vec<Stmt<Elab>>, Hole),                // type(*stmt)
    Lam(Ident, Box<Elab>, Hole),              // type(*ident) -> type(*elab)
    App(Box<Elab>, Box<Elab>, Hole),          // type(*elab *elab)
    Let(Ident, Box<Elab>, Box<Elab>, Hole),   // type(type(*ident) := type(*elab) in *elab)
    Match(Box<Elab>, Vec<(Pat, Elab)>, Hole), // type(match *elab with $pat => *elab

    // *internal*
    Closure(Vec<(String, Elab)>, Ident, Box<Elab>, Hole),
}

impl Ident {
    pub fn new(name: &'static str) -> Self {
        Ident(name)
    }
}

impl std::fmt::Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::fmt::Display for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Kind::Any => write!(f, "*"),
            Kind::Fun(head, tail) => write!(f, "{head} -> {tail}"),
        }
    }
}

impl From<&str> for Ident {
    fn from(value: &str) -> Self {
        Ident(crate::leak::leak_string(value.to_string()))
    }
}

impl From<String> for Ident {
    fn from(value: String) -> Self {
        Ident(crate::leak::leak_string(value))
    }
}
