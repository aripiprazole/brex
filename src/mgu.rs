use crate::typing::{App, Hole, Ty, Var, HasKind};
use crate::Result;

pub fn unify(a_ref: Hole, b_ref: Hole) -> Result<()> {
    use App::*;

    match (a_ref.unwrap(), b_ref.unwrap()) {
        (Ty::App(Call(a, b) | Arrow(a, b)), Ty::App(Call(a2, b2) | Arrow(a2, b2))) => {
            unify(*a, *a2)?;
            unify(*b, *b2)?;
        }
        (Ty::App(Array(a)), Ty::App(Array(a2))) => {
            unify(*a, *a2)?;
        }
        (Ty::Cons(a), Ty::Cons(b)) if a == b => {}
        (Ty::Var(Var(name, kind)), t) | (t, Ty::Var(Var(name, kind))) => match t {
            Ty::Var(Var(tname, ..)) if tname == name => {}
            _ if t.free_vars().contains(name.0) => {
                return Err(format!("occurs check failed: {name} in {t}"));
            }
            _ if kind.clone() != t.kind() => {
                return Err(format!("cannot unify kinds {kind} and {}", t.kind()));
            }
            _ => {
                a_ref.set(t.clone());
            }
        },
        (a, b) if a.kind() != b.kind() => {
            return Err(format!("cannot unify kinds {a} and {b}"));
        }
        (a, b) => {
            return Err(format!("cannot unify {a} and {b}"));
        }
    }

    Ok(())
}
