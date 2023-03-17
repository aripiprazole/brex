use crate::syntax::{Elab, Ident, Term};
use crate::typing::{Hole, Instantiate, Kind, Qual, Scheme, Ty, Var};
use crate::Result;

#[derive(Clone, Default)]
pub struct Infer {
    pub n: usize,
    pub fields: im::HashMap<String, Scheme, fxhash::FxBuildHasher>,
}

impl Infer {
    pub fn infer_exp(&mut self, term: Term) -> Result<Elab> {
        match term {
            Term::Nil => todo!(),
            Term::Prim(prim) => Ok(Elab::Prim(prim)),
            Term::Atom(Ident(name)) => {
                let scheme = self
                    .fields
                    .get(name)
                    .ok_or(format!("unbound variable: {}", name))?;

                let Qual(predicates, ty) = self.fresh_inst(scheme.clone());

                Ok(Elab::Atom(Ident(name), predicates, ty.into()))
            }
            Term::Do(_) => todo!(),
            Term::As(_, _) => todo!(),
            Term::Lam(_, _) => todo!(),
            Term::App(box callee, box arg) => {
                let callee = self.infer_exp(callee)?;
                let arg = self.infer_exp(arg)?;
                let ty: Hole = self.fresh_var(Kind::Any).into();

                crate::mgu::unify(Ty::arrow(arg.hole(), ty.clone()).into(), callee.hole())?;

                Ok(Elab::App(callee.into(), arg.into(), ty))
            }
            Term::Let(ident @ Ident(name), box value, box term) => {
                let mut env = self.clone();
                let value = env.infer_exp(value)?;
                let scheme = value.hole().extract().quantify();
                env.fields.insert(name.into(), scheme);
                let term = env.infer_exp(term)?;
                let hole = term.hole();

                Ok(Elab::Let(ident, value.into(), term.into(), hole))
            }
            Term::Match(_, _) => todo!(),
            Term::Closure(_, _, _) => todo!(),
        }
    }

    pub fn fresh_var(&mut self, kind: Kind) -> Ty {
        let n = self.n;
        self.n += 1;
        Ty::Var(Var(format!("v{n}").into(), kind))
    }

    pub fn fresh_inst(&mut self, scheme: Scheme) -> Qual<Ty> {
        let types = scheme
            .0
            .into_iter()
            .map(|kind| self.fresh_var(kind))
            .collect();

        scheme.1.instantiate(types)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typing;

    macro_rules! run_typing {
        ($s:expr, {$($names:ident: $types:expr),+}) => {{
            let mut ty_env = Infer::default();
            $(ty_env.fields.insert(stringify!($names).into(), $types.into());)+
            run_typing!($s, ty_env)
        }};
        ($s:expr, $te:expr) => {{
            let exp = crate::parsing::asena::TermParser::new().parse($s).unwrap();
            let term = exp.try_into().unwrap();

            $te.infer_exp(term).unwrap()
        }};
    }

    #[test]
    fn infers_with_call() {
        let result = run_typing!("(let (x 'hello world') (println x))", {
            println: Ty::arrow(typing::STRING_HOLE.clone(), typing::NIL_HOLE.clone()).quantify()
        });

        println!("{}", result.hole());
    }
}
