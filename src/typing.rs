use crate::spaced::{Mode, Spaced};
use crate::syntax::{Elab, Ident, Prim};

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
pub struct Var(pub Ident, pub Kind);

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
pub struct Scheme(pub Vec<Kind>, pub Qual<Ty>);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Hole(pub *mut Ty);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Qual<A>(pub Vec<Pred>, pub A);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Pred(pub Ty, pub Ident);

/// Represents a type class by a pair of lists, one containing super class names,
/// and the second containing the instance declarations.
///
/// Example of `Ord`:
/// > ([Ident "Eq"], [[] :=> Has Int (Ident "Ord")])
///   This example captures the fact that `Eq` is a super class of `Ord`,
///   and `Ord` has a instance for the type `Int`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Class(pub Vec<Ident>, pub Vec<Inst>);

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct ClassEnv {
    pub classes: im::HashMap<Ident, Class, fxhash::FxBuildHasher>,
    pub defaults: Vec<Ty>,
}

pub type Inst = Qual<Pred>;

/// | Ambiguity is when a type scheme ps :=> τ, ps contains quantified variables
/// that not appears in τ.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Ambiguity(pub Var, pub Vec<Pred>);

pub trait HasKind {
    fn kind(&self) -> Kind;
}

pub trait Instantiate {
    fn instantiate(&self, types: Vec<Ty>) -> Self;
}

impl Kind {
    pub fn apply(&self, ty: &Ty) -> Kind {
        match self {
            Kind::Any => ty.kind(),
            Kind::Fun(_, box tail) => tail.clone(),
        }
    }
}

impl Elab {
    pub fn hole(&self) -> Hole {
        match self {
            Elab::Nil => *NIL_HOLE,
            Elab::Prim(Prim::True) => *BOOL_HOLE,
            Elab::Prim(Prim::False) => *BOOL_HOLE,
            Elab::Prim(Prim::Decimal(..)) => *DECIMAL_HOLE,
            Elab::Prim(Prim::Int(..)) => *INT_HOLE,
            Elab::Prim(Prim::String(..)) => *STRING_HOLE,
            Elab::Atom(_, _, ty) => *ty,
            Elab::Do(_, ty) => *ty,
            Elab::Lam(_, _, ty) => *ty,
            Elab::App(_, _, ty) => *ty,
            Elab::Let(_, _, _, ty) => *ty,
            Elab::Match(_, _, ty) => *ty,
            Elab::Closure(_, _, _, ty) => *ty,
        }
    }
}

impl Ty {
    pub const BOOL: Ty = Ty::Cons(Cons::Bool);
    pub const INT: Ty = Ty::Cons(Cons::Int);
    pub const DECIMAL: Ty = Ty::Cons(Cons::Decimal);
    pub const NAT: Ty = Ty::Cons(Cons::Nat);
    pub const CHAR: Ty = Ty::Cons(Cons::Char);
    pub const STRING: Ty = Ty::Cons(Cons::String);
    pub const NIL: Ty = Ty::Cons(Cons::Nil);

    pub fn arrow(head: Hole, tail: Hole) -> Self {
        Self::App(App::Arrow(head, tail))
    }

    pub fn quantify(&self) -> Scheme {
        Scheme(vec![], Qual(vec![], self.clone()))
    }

    pub fn free_vars(&self) -> im::HashSet<&str> {
        use App::*;
        match self {
            Ty::Var(Var(Ident(var), ..)) => im::hashset![*var],
            Ty::App(Array(ty)) => ty.free_vars(),
            Ty::App(Arrow(a, b) | Call(a, b)) => a.free_vars().relative_complement(b.free_vars()),
            Ty::Gen(_) | Ty::Cons(_) => im::hashset![],
        }
    }
}

impl Hole {
    pub fn new(ty: Ty) -> Self {
        Self(Box::leak(Box::new(ty)))
    }

    pub fn set(&self, ty: Ty) {
        unsafe {
            *self.0 = ty;
        }
    }

    pub fn unwrap(&self) -> &Ty {
        unsafe { self.0.as_ref().unwrap() }
    }
}

impl Instantiate for Scheme {
    fn instantiate(&self, _types: Vec<Ty>) -> Self {
        todo!()
    }
}

impl Instantiate for Hole {
    fn instantiate(&self, _types: Vec<Ty>) -> Self {
        todo!()
    }
}

impl Instantiate for Pred {
    fn instantiate(&self, _types: Vec<Ty>) -> Self {
        todo!()
    }
}

impl Instantiate for Ty {
    fn instantiate(&self, _types: Vec<Ty>) -> Self {
        self.clone()
    }
}

impl<A: Instantiate> Instantiate for Qual<A> {
    fn instantiate(&self, types: Vec<Ty>) -> Self {
        Qual(self.0.instantiate(types.clone()), self.1.instantiate(types))
    }
}

impl<A: Instantiate> Instantiate for Vec<A> {
    fn instantiate(&self, types: Vec<Ty>) -> Self {
        self.iter().map(|a| a.instantiate(types.clone())).collect()
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
        self.unwrap().kind()
    }
}

impl std::fmt::Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use App::*;
        use Cons::*;

        match self {
            Ty::Gen(i) => write!(f, "'{}", get_new_sym(*i).unwrap_or_default()),
            Ty::Var(Var(name, kind)) => write!(f, "(: '{name} {kind})"),
            Ty::App(Call(a, b)) => match ((*a).into(), (*b).into()) {
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
        write!(f, "{}", self.unwrap())
    }
}

impl std::ops::Deref for Hole {
    type Target = Ty;

    fn deref(&self) -> &Self::Target {
        unsafe { self.0.as_ref().unwrap() }
    }
}

impl From<Hole> for Ty {
    fn from(hole: Hole) -> Self {
        hole.unwrap().clone()
    }
}

impl From<Ty> for Hole {
    fn from(ty: Ty) -> Self {
        Self::new(ty)
    }
}

unsafe impl Sync for Hole {}

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

lazy_static! {
    pub static ref BOOL_HOLE: Hole = Hole::new(Ty::BOOL);
    pub static ref INT_HOLE: Hole = Hole::new(Ty::INT);
    pub static ref DECIMAL_HOLE: Hole = Hole::new(Ty::DECIMAL);
    pub static ref NAT_HOLE: Hole = Hole::new(Ty::NAT);
    pub static ref CHAR_HOLE: Hole = Hole::new(Ty::CHAR);
    pub static ref STRING_HOLE: Hole = Hole::new(Ty::STRING);
    pub static ref NIL_HOLE: Hole = Hole::new(Ty::NIL);
}
