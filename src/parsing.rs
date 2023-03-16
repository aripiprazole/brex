use crate::syntax::Prim;

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

lalrpop_mod!(
    #[allow(clippy::all)]
    #[allow(unused)]
    pub asena
);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::Exp;

    #[test]
    fn string_parses() {
        let string = asena::TermParser::new().parse("'hello'").unwrap();

        assert_eq!(string, Exp::Prim(Prim::String("hello".to_string())));
    }

    #[test]
    fn int_parses() {
        let int = asena::TermParser::new().parse("1").unwrap();

        assert_eq!(int, Exp::Prim(Prim::Int(1)));
    }

    #[test]
    fn decimal_parses() {
        let decimal = asena::TermParser::new().parse("1.0").unwrap();

        assert_eq!(decimal, Exp::Prim(Prim::Decimal(1, 0)));
    }

    #[test]
    fn atom_parses() {
        let atom = asena::TermParser::new().parse("some").unwrap();

        assert_eq!(atom, Exp::Atom("some".into()));
    }

    #[test]
    fn cons_parses() {
        let cons = asena::TermParser::new().parse("(some thing)").unwrap();

        assert_eq!(
            cons,
            Exp::Cons(
                Exp::Atom("some".into()).into(),
                Exp::Cons(Exp::Atom("thing".into()).into(), Exp::Nil.into()).into()
            )
        );
    }

    #[test]
    fn nil_parses() {
        let nil = asena::TermParser::new().parse("()").unwrap();

        assert_eq!(nil, Exp::Nil);
    }
}
