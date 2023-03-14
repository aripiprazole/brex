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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Elab {
    Prim(Prim),

    // expressions
    Nil,
    Atom(Ident, Ty),                    // type(*ident)
    Do(Vec<Stmt<Elab>>),                // type(*stmt)
    Lam(Ident, Box<Elab>),              // type(*ident) -> type(*elab)
    App(Box<Elab>, Box<Elab>),          // type(*elab *elab)
    Let(Ident, Box<Elab>, Box<Elab>),   // type(type(*ident) := type(*elab) in *elab)
    Match(Box<Elab>, Vec<(Pat, Elab)>), // type(match *elab with $pat => *elab

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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Span<A>(A, pub std::ops::Range<usize>);

pub type Result<V, E = String> = std::result::Result<V, E>;

pub trait HasKind {
    fn kind(&self) -> Kind;
}

pub trait Instantiate {
    fn instantiate(&self, types: Vec<Ty>) -> Self;
}

impl Exp {
    pub fn spec(self) -> Result<Term> {
        use crate::Exp::*;
        use crate::Prim::*;

        match self {
            Nil => Ok(Term::Nil),
            Prim(prim) => Ok(Term::Prim(prim)),
            Atom(Ident(ident)) if ident == "True" => Ok(Term::Prim(True)),
            Atom(Ident(ident)) if ident == "False" => Ok(Term::Prim(False)),
            Atom(ident) => Ok(Term::Atom(ident)),
            Cons(box Nil, ..) => Ok(Term::Nil), // error
            Cons(box Prim(False | True | Int(..) | Decimal(..)), ..) => {
                todo!() // error
            }
            Cons(box Atom(Ident(name)), box tail) => Exp::specialize_cons(&name, tail.try_into()?),
            Cons(head, tail) => Ok(Term::App(head.spec()?.into(), tail.spec()?.into())),
        }
    }

    fn specialize_cons(name: &str, args: Vec<Term>) -> Result<Term> {
        match (name, args.as_slice()) {
            ("as", [value, Term::Atom(type_name)]) => {
                Ok(Term::As(Box::new(value.clone()), type_name.clone()))
            }
            ("lambda", [Term::Atom(name), term]) => {
                Ok(Term::Lam(name.clone(), Box::new(term.clone())))
            }
            ("let", [Term::App(box Term::Atom(name), value), term]) => Ok(Term::Let(
                name.clone(),
                value.clone(),
                Box::new(term.clone()),
            )),
            ("do", stmts @ &[..]) => {
                let smts = stmts
                    .iter()
                    .map(|term| Vec::<Term>::try_from(term.clone()))
                    .collect::<Result<Vec<Vec<Term>>>>()?
                    .iter()
                    .map(|args| match args.as_slice() {
                        [Term::Atom(Ident(arrow)), Term::Atom(name), value] if arrow == "<-" => {
                            Ok(Stmt::Binding(name.clone(), value.clone()))
                        }
                        [value] => Ok(Stmt::Eval(value.clone())),
                        _ => Err(format!("invalid statement: {:?}", args)),
                    })
                    .collect::<Result<Vec<Stmt<Term>>>>()?;

                Ok(Term::Do(smts))
            }

            _ => todo!(),
        }
    }
}

impl TryFrom<Term> for Vec<Term> {
    type Error = String;

    fn try_from(value: Term) -> Result<Vec<Term>, Self::Error> {
        let mut list = vec![];
        let mut current = value;

        while let Term::App(box head, tail) = current {
            list.push(head);
            current = *tail;
        }

        Ok(list)
    }
}

impl TryFrom<Exp> for Vec<Term> {
    type Error = String;

    fn try_from(value: Exp) -> Result<Vec<Term>, Self::Error> {
        let mut list = vec![];
        let mut current = value;

        while let Exp::Cons(head, tail) = current {
            list.push(head.spec()?);
            current = *tail;
        }

        Ok(list)
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

#[macro_use]
extern crate lalrpop_util;

lalrpop_mod!(
    #[allow(clippy::all)]
    #[allow(unused)]
    pub asena
);

pub fn leak_string(s: String) -> &'static str {
    Box::leak(s.into_boxed_str())
}

pub fn parse_number(str: &str) -> Result<Prim, String> {
    let mut parts = str.split('.');
    let int = parts.next().ok_or("no integer part")?;
    let int = int
        .parse::<i128>()
        .map_err(|_| "integer part is not a number")?;

    match parts.next() {
        Some(frac) => {
            let frac = frac
                .parse::<i128>()
                .map_err(|_| "frac part is not a number")?;

            Ok(Prim::Decimal(int, frac))
        }
        None => Ok(Prim::Int(int)),
    }
}

fn main() {
    asena::TermParser::new().parse("1.0").unwrap();
}

#[cfg(test)]
mod parser_tests {
    use super::*;

    #[test]
    fn string_parses() {
        let string = crate::asena::TermParser::new().parse("'hello'").unwrap();

        assert_eq!(string, Exp::Prim(Prim::String("hello".to_string())));
    }

    #[test]
    fn int_parses() {
        let int = crate::asena::TermParser::new().parse("1").unwrap();

        assert_eq!(int, Exp::Prim(Prim::Int(1)));
    }

    #[test]
    fn decimal_parses() {
        let decimal = crate::asena::TermParser::new().parse("1.0").unwrap();

        assert_eq!(decimal, Exp::Prim(Prim::Decimal(1, 0)));
    }

    #[test]
    fn atom_parses() {
        let atom = crate::asena::TermParser::new().parse("some").unwrap();

        assert_eq!(atom, Exp::Atom(Ident("some".to_string())));
    }

    #[test]
    fn cons_parses() {
        let cons = crate::asena::TermParser::new()
            .parse("(some thing)")
            .unwrap();

        assert_eq!(
            cons,
            Exp::Cons(
                Box::new(Exp::Atom(Ident("some".to_string()))),
                Box::new(Exp::Cons(
                    Box::new(Exp::Atom(Ident("thing".to_string()))),
                    Box::new(Exp::Nil),
                ))
            )
        );
    }

    #[test]
    fn nil_parses() {
        let nil = crate::asena::TermParser::new().parse("()").unwrap();

        assert_eq!(nil, Exp::Nil);
    }
}
