#![feature(associated_type_defaults, box_patterns)]

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Ident(&'static str);

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
    Decimal, // Decimal
    Nat,     // Nat
    Char,    // Char
    String,  // String (alias -> [Char])
    Nil,     // ()
    Atom(Ident),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Var(Ident, Kind);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum App {
    Call(Hole, Hole),  // τ τ
    Arrow(Hole, Hole), // τ -> τ
    Array(Hole),       // [τ]
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

pub enum Mode {
    Interperse,
    Before,
}

pub struct Spaced<'a, T>(pub Mode, pub &'static str, pub &'a [T])
where
    T: std::fmt::Display;

pub type Result<V, E = String> = std::result::Result<V, E>;

pub trait HasKind {
    fn kind(&self) -> Kind;
}

pub trait Instantiate {
    fn instantiate(&self, types: Vec<Ty>) -> Self;
}

pub trait Spec<T> {
    fn spec(self) -> Result<T>;
}

impl TryFrom<Exp> for Decl<Term> {
    type Error = String;

    fn try_from(value: Exp) -> Result<Self, Self::Error> {
        use crate::Exp::*;

        if let Cons(box Atom(Ident(name)), box tail) = value.clone() {
            let args: Vec<_> = tail.try_into()?;

            return match (name, args.as_slice()) {
                ("class", &[..]) => todo!(),
                ("impl", &[..]) => todo!(),
                _ => Ok(Decl::Eval(value.try_into()?)),
            };
        }

        Ok(Decl::Eval(value.try_into()?))
    }
}

impl TryFrom<Vec<Term>> for Stmt<Term> {
    type Error = String;

    fn try_from(value: Vec<Term>) -> Result<Self, Self::Error> {
        use crate::Term::*;

        match value.as_slice() {
            [Atom(Ident("<-")), Atom(name), value] => {
                Ok(Stmt::Binding(name.clone(), value.clone()))
            }
            [value] => Ok(Stmt::Eval(value.clone())),
            _ => Err(format!("invalid statement: {:?}", value)),
        }
    }
}

impl TryFrom<Exp> for Term {
    type Error = String;

    fn try_from(value: Exp) -> Result<Self, Self::Error> {
        use crate::Exp::*;
        use crate::Prim::*;

        match value {
            Nil => Ok(Term::Nil),
            Prim(prim) => Ok(Term::Prim(prim)),
            Atom(Ident("True")) => Ok(Term::Prim(True)),
            Atom(Ident("False")) => Ok(Term::Prim(False)),
            Atom(ident) => Ok(Term::Atom(ident)),
            Cons(box Nil, ..) => Err("invalid callee: nil. can't call nil".to_string()),
            Cons(head @ box Prim(..), ..) => Err(format!(
                "invalid callee: {head:?}. can't call primitive value"
            )),
            Cons(box Atom(Ident(name)), box tail) => call_spec(name, tail.try_into()?),
            Cons(box head, box tail) => Ok(Term::App(
                Box::new(head.try_into()?),
                Box::new(tail.try_into()?),
            )),
        }
    }
}

fn call_spec(name: &str, args: Vec<Term>) -> Result<Term> {
    use Term::*;

    match (name, args.as_slice()) {
        ("as", [value, Atom(type_name)]) => Ok(As(value.clone().into(), type_name.clone())),
        ("lambda", [Atom(name), term]) => Ok(Lam(name.clone(), term.clone().into())),
        ("let", [App(box Atom(name), value), term]) => {
            Ok(Let(name.clone(), value.clone(), term.clone().into()))
        }
        ("do", stmts @ [..]) => {
            let smts = stmts
                .iter()
                .map(|stmt| {
                    let stmt: Vec<_> = stmt.clone().try_into()?;
                    let stmt: Stmt<_> = stmt.try_into()?;

                    Ok(stmt)
                })
                .collect::<Result<_>>()?;

            Ok(Term::Do(smts))
        }

        _ => todo!(),
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

impl TryFrom<Box<Exp>> for Vec<Term> {
    type Error = String;

    fn try_from(value: Box<Exp>) -> Result<Vec<Term>, Self::Error> {
        TryFrom::<Exp>::try_from(*value)
    }
}

impl TryFrom<Exp> for Vec<Term> {
    type Error = String;

    fn try_from(value: Exp) -> Result<Vec<Term>, Self::Error> {
        let mut list = vec![];
        let mut current = value;

        while let Exp::Cons(box head, tail) = current {
            list.push(head.try_into()?);
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
            App::Array(_) => Kind::Any,
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

impl<'a, T> std::fmt::Display for Spaced<'a, T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Spaced(Mode::Interperse, string, slice) => {
                if !slice.is_empty() {
                    write!(f, "{}", slice[0])?;
                    for element in &slice[1..] {
                        write!(f, "{string}{element}")?;
                    }
                }
            }
            Spaced(Mode::Before, string, slice) => {
                for element in slice.iter() {
                    write!(f, "{string}{element}")?;
                }
            }
        }
        Ok(())
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

impl std::fmt::Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use App::*;
        use Cons::*;

        match self {
            Ty::Gen(i) => write!(f, "'{}", get_new_sym(*i).unwrap_or_default()),
            Ty::Var(Var(name, kind)) => write!(f, "(: '{name} {kind})"),
            Ty::App(Call(a, b)) => match (a.clone().into(), b.clone().into()) {
                (a @ Ty::App(..), b @ Ty::App(..)) => write!(f, "(({a}) ({b}))"),
                (a @ Ty::App(..), b) => write!(f, "(({a}) {b})"),
                (a, b @ Ty::App(..)) => write!(f, "({a} ({b}))"),
                (a, b) => write!(f, "({a} {b})"),
            },
            Ty::App(Arrow(a, b)) => write!(f, "(-> {a} {b})"),
            Ty::App(Array(repr)) => write!(f, "[{repr}]"),
            Ty::Cons(Bool) => write!(f, "Bool"),
            Ty::Cons(Int) => write!(f, "Int"),
            Ty::Cons(Decimal) => write!(f, "Decimal"),
            Ty::Cons(Nat) => write!(f, "Nat"),
            Ty::Cons(Char) => write!(f, "Char"),
            Ty::Cons(String) => write!(f, "String"),
            Ty::Cons(Nil) => write!(f, "()"),
            Ty::Cons(Atom(name)) => write!(f, "{name}"),
        }
    }
}

impl std::fmt::Display for Pred {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} {})", self.1, self.0)
    }
}

impl<A: std::fmt::Display> std::fmt::Display for Qual<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let predicates = Spaced(Mode::Interperse, ", ", &self.0);

        write!(f, "(=> {} {})", predicates, self.1)
    }
}

impl std::fmt::Display for Hole {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::ops::Deref for Hole {
    type Target = Ty;

    fn deref(&self) -> &Self::Target {
        self.0.as_ref()
    }
}

impl From<Hole> for Ty {
    fn from(hole: Hole) -> Self {
        *hole.0
    }
}

impl From<Ty> for Hole {
    fn from(ty: Ty) -> Self {
        Self::new(ty)
    }
}

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

#[macro_use]
extern crate lalrpop_util;

fn get_new_sym(i: usize) -> Option<String> {
    let prefix_size = ((i as f64).log(26.0) + 1.0).floor() as usize;
    let base = 26usize.pow(prefix_size as u32);

    if i == 0 {
        return Some("a".into());
    } else if i > base {
        return None;
    }

    let prefix = (0..prefix_size)
        .map(|j| ((i / 26usize.pow(j as u32)) % 26) as u8 + b'a')
        .collect::<Vec<_>>();

    String::from_utf8(prefix).ok()
}

fn main() {
    println!(
        "{}",
        Qual(
            vec![Pred(Ty::Cons(Cons::Atom(Ident("Int"))), Ident("Parse"))],
            Ty::App(App::Arrow(
                Ty::Cons(Cons::Atom(Ident("String"))).into(),
                Ty::Cons(Cons::Atom(Ident("Int"))).into()
            ))
        )
    );
    asena::TermParser::new().parse("1.0").unwrap();
}

lalrpop_mod!(
    #[allow(clippy::all)]
    #[allow(unused)]
    pub asena
);

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

        assert_eq!(atom, Exp::Atom(Ident("some")));
    }

    #[test]
    fn cons_parses() {
        let cons = crate::asena::TermParser::new()
            .parse("(some thing)")
            .unwrap();

        assert_eq!(
            cons,
            Exp::Cons(
                Exp::Atom(Ident("some")).into(),
                Exp::Cons(Exp::Atom(Ident("thing")).into(), Exp::Nil.into()).into()
            )
        );
    }

    #[test]
    fn nil_parses() {
        let nil = crate::asena::TermParser::new().parse("()").unwrap();

        assert_eq!(nil, Exp::Nil);
    }
}
