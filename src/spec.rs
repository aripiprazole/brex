use crate::syntax::{Decl, Exp, Ident, Stmt, Term};
use crate::Result;

impl TryFrom<Exp> for Decl<Term> {
    type Error = String;

    fn try_from(value: Exp) -> Result<Self, Self::Error> {
        use Exp::*;

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
        use Term::*;

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
        use crate::syntax::Prim::*;
        use Exp::*;

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

fn call_spec(name: &'static str, args: Vec<Term>) -> Result<Term> {
    use Term::*;

    match (name, args.as_slice()) {
        ("as", [value, Atom(type_name)]) => Ok(As(value.clone().into(), type_name.clone())),
        ("lambda", [Atom(name), term]) => Ok(Lam(name.clone(), term.clone().into())),
        ("let", [App(box App(box Atom(name), value), box Nil), App(box term, box Nil)]) => {
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

        (name, args) => Ok(args.iter().rfold(Term::Nil, |acc, arg| {
            App(
                Box::new(App(Box::new(Atom(Ident(name))), Box::new(arg.clone()))),
                Box::new(acc),
            )
        })),
    }
}
