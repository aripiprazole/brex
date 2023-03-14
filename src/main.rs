#![feature(associated_type_defaults, try_trait_v2, box_patterns)]

use std::ops::Deref;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Ident(String);

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
pub enum Exp {
    // primitives
    True,
    False,
    Char(char),
    Decimal(i128, i128),
    Int(i128),

    // constructs
    Atom(Ident),
    App(Box<Exp>, Box<Exp>),
    String(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Stmt<E> {
    pub name: Option<Ident>,
    pub value: Box<E>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    // primitives
    True,
    False,
    Char(char),
    Decimal(i128, i128),
    Int(i128),

    // expressions
    Var(Ident),
    As(Box<Term>, Ident),
    Lam(Ident, Box<Term>),
    App(Box<Term>, Box<Term>),
    Let(Ident, Box<Term>, Box<Term>),
    Do(Vec<Stmt<Term>>),

    // *internal*
    Closure(Vec<(String, Term)>, Ident, Box<Term>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Elab {
    // primitives
    True,                // Bool
    False,               // Bool
    Char(char),          // Char
    Decimal(i128, i128), // Decimal
    Int(i128),           // Int

    // expressions
    Var(Ident, Ty),                   // type(*ident)
    Lam(Ident, Box<Elab>),            // type(*ident) -> type(*elab)
    App(Box<Elab>, Box<Elab>),        // type(*elab *elab)
    Let(Ident, Box<Elab>, Box<Elab>), // type(type(*ident) := type(*elab) in *elab)
    Do(Vec<Stmt<Elab>>),              // type(*stmt)

    // *internal*
    Closure(Vec<(String, Elab)>, Ident, Box<Elab>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Qual<A>(Vec<Pred>, A);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Pred(Ty, Ident);

/// Represents a type class by a pair of lists, one containing super class names,
/// and the second containing the instance declarations.
///
/// Example of `Ord`:
/// > ([Ident "Eq"], [[] :=> Has Int (Ident "Ord")])
///   This example captures the fact that `Eq` is a super class of `Ord`,
///   and `Ord` has a instance for the type `Int`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Class(Vec<Ident>, Vec<Inst>);

pub type Inst = Qual<Pred>;

/// | Ambiguity is when a type scheme ps :=> τ, ps contains quantified variables
/// that not appears in τ.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Ambiguity(Var, Vec<Pred>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ClassEnv {
    pub classes: im::HashMap<Ident, Class, fxhash::FxBuildHasher>,
    pub defaults: Vec<Ty>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Kind {
    Any,                       // *
    Fun(Box<Kind>, Box<Kind>), // * -> *
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Cons {
    Bool,    // Bool
    Int,     // Int
    Decimal, // Int
    Nat,     // Nat
    Char,    // Char
    String,  // String (alias -> [Char])
    Unit,    // ()
    Atom(Ident),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Var(Ident, Kind);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum App {
    Call(Hole, Hole),  // τ τ
    Arrow(Hole, Hole), // τ -> τ
    Array(Hole, Hole), // [τ]
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    Gen(usize), // *internal*
    App(App),   // τ τ
    Var(Var),   // 'α
    Cons(Cons), // α
}

/// Type schemes are used to describe qualified types.
/// Each Ty::Gen that appears in qual represents a generic that the kind is given
// by `kinds[n]`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Scheme(Vec<Kind>, Qual<Ty>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Hole(Box<Ty>);

pub struct Lexer;

pub struct Parser;

pub type Result<V, E = String> = std::result::Result<V, E>;

pub trait HasKind {
    fn kind(&self) -> Kind;
}

pub trait Instantiate {
    fn instantiate(&self, types: Vec<Ty>) -> Self;
}

impl Lexer {
    pub fn new(_code: String) -> Self {
        todo!()
    }

    pub fn lex(&self) -> Parser {
        todo!()
    }
}

impl From<Lexer> for Parser {
    fn from(_lexer: Lexer) -> Self {
        todo!()
    }
}

impl Parser {
    pub fn parse(&self) -> Result<Exp> {
        todo!()
    }
}

impl Exp {
    pub fn spec(&self) -> Result<Term> {
        todo!()
    }
}

impl Term {
    pub fn elab(&self) -> Result<Elab> {
        todo!()
    }
}

impl HasKind for Cons {
    fn kind(&self) -> Kind {
        Kind::Any
    }
}

impl HasKind for Var {
    fn kind(&self) -> Kind {
        Kind::Any
    }
}

impl HasKind for App {
    fn kind(&self) -> Kind {
        match self {
            App::Arrow(head, tail) => Kind::Fun(Box::new(head.kind()), Box::new(tail.kind())),
            App::Call(head, ty) => head.kind().apply(ty.unwrap()),
            App::Array(_, _) => Kind::Any,
        }
    }
}

impl HasKind for Ty {
    fn kind(&self) -> Kind {
        match self {
            Ty::App(app) => app.kind(),
            Ty::Gen(_) | Ty::Var(_) | Ty::Cons(_) => Kind::Any,
        }
    }
}

impl HasKind for Hole {
    fn kind(&self) -> Kind {
        self.0.kind()
    }
}

impl Kind {
    pub fn apply(&self, ty: &Ty) -> Kind {
        match self {
            Kind::Any => ty.kind(),
            Kind::Fun(_, box tail) => tail.clone(),
        }
    }
}

impl Hole {
    pub fn new(ty: Ty) -> Self {
        Self(Box::new(ty))
    }

    pub fn set(&mut self, ty: Ty) {
        *self.0 = ty;
    }

    pub fn unwrap(&self) -> &Ty {
        self.0.as_ref()
    }
}

impl Deref for Hole {
    type Target = Ty;

    fn deref(&self) -> &Self::Target {
        self.0.as_ref()
    }
}

fn main() {
    let elab = Lexer::new("(println \"hello, world\")".to_string())
        .lex()
        .parse()
        .unwrap()
        .spec()
        .unwrap()
        .elab()
        .unwrap();

    println!("{:#?}", elab)
}
