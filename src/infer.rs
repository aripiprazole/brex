use crate::leak::leak_string;
use crate::syntax::{Elab, Ident, Term};
use crate::typing::{Hole, Instantiate, Kind, Qual, Scheme, Ty, Var};
use crate::Result;

#[derive(Clone, Default)]
pub struct TyEnv {
    pub n: usize,
    pub fields: im::HashMap<String, Scheme, fxhash::FxBuildHasher>,
}

impl TyEnv {
    pub fn fresh_var(&mut self, kind: Kind) -> Ty {
        let n = self.n;
        self.n += 1;
        Ty::Var(Var(Ident(leak_string(format!("v{n}"))), kind))
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

pub fn infer_exp(term: Term, env: &mut TyEnv) -> Result<Elab> {
    match term {
        Term::Nil => todo!(),
        Term::Prim(prim) => Ok(Elab::Prim(prim)),
        Term::Atom(Ident(name)) => {
            let scheme = env
                .fields
                .get(name)
                .ok_or(format!("unbound variable: {}", name))?;

            let Qual(predicates, ty) = env.fresh_inst(scheme.clone());

            Ok(Elab::Atom(Ident(name), predicates, ty.into()))
        }
        Term::Do(_) => todo!(),
        Term::As(_, _) => todo!(),
        Term::Lam(_, _) => todo!(),
        Term::App(box callee, box arg) => {
            let callee = infer_exp(callee, env)?;
            let arg = infer_exp(arg, env)?;
            let ty: Hole = env.fresh_var(Kind::Any).into();

            crate::mgu::unify(Ty::arrow(arg.hole(), ty).into(), callee.hole())?;

            Ok(Elab::App(callee.into(), arg.into(), ty))
        }
        Term::Let(ident @ Ident(name), box value, box term) => {
            let mut env = env.clone();
            let value = infer_exp(value, &mut env)?;
            env.fields.insert(name.to_string(), value.hole().quantify());
            let term = infer_exp(term, &mut env)?;
            let hole = term.hole();

            Ok(Elab::Let(ident, value.into(), term.into(), hole))
        }
        Term::Match(_, _) => todo!(),
        Term::Closure(_, _, _) => todo!(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typing;

    macro_rules! run_typing {
        ($s:expr, {$($names:ident: $types:expr),+}) => {{
            let mut ty_env = TyEnv::default();
            $(ty_env.fields.insert(stringify!($names).into(), $types.into());)+
            run_typing!($s, ty_env)
        }};
        ($s:expr, $te:expr) => {{
            let exp = crate::parsing::asena::TermParser::new().parse($s).unwrap();
            let term = exp.try_into().unwrap();

            infer_exp(term, &mut $te).unwrap()
        }};
    }

    #[test]
    fn infers_with_call() {
        let result = run_typing!("(let (x 'hello world') (println x))", {
            println: Ty::arrow(*typing::STRING_HOLE, *typing::NIL_HOLE).quantify()
        });

        println!("{}", result.hole());
    }
}
