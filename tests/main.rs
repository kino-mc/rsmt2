#![allow(unused_imports)]
use error_chain::bail;
use rsmt2::{parse::*, *};

type Typ = String;
type Ident = String;
type Expr = String;
type Val = bool;

#[derive(Clone, Copy)]
struct Parser;
impl<'a> ValueParser<Val, &'a str> for Parser {
    fn parse_value(self, input: &'a str) -> SmtRes<Val> {
        match input {
            "true" => Ok(true),
            "false" => Ok(false),
            _ => bail!("unexpected value `{}`", input),
        }
    }
}
impl<'a> ExprParser<Expr, (), &'a str> for Parser {
    fn parse_expr(self, input: &'a str, _: ()) -> SmtRes<Expr> {
        Ok(input.into())
    }
}
impl<'a> IdentParser<Ident, Typ, &'a str> for Parser {
    fn parse_ident(self, input: &'a str) -> SmtRes<Ident> {
        Ok(input.into())
    }
    fn parse_type(self, input: &'a str) -> SmtRes<Typ> {
        Ok(input.into())
    }
}
impl<'a> ModelParser<Ident, Typ, Val, &'a str> for Parser {
    fn parse_value(
        self,
        input: &'a str,
        _id: &Ident,
        _args: &[(Ident, Typ)],
        _out: &Typ,
    ) -> SmtRes<Val> {
        match input {
            "true" => Ok(true),
            "false" => Ok(false),
            _ => bail!("unexpected value `{}`", input),
        }
    }
}

#[cfg(test)]
pub mod cvc4 {
    use super::*;
    #[test]
    fn set_logic() {
        let conf = SmtConf::cvc4();
        let mut solver = Solver::new(conf, Parser).expect("solver creation");
        solver
            .set_logic(::rsmt2::Logic::QF_UF)
            .expect("setting logic");
    }

    #[test]
    fn scenario_1() {
        let mut conf = SmtConf::cvc4();
        conf.models();
        let mut solver = Solver::new(conf, Parser).expect("solver creation");
        solver
            .declare_const("a", "Bool")
            .expect("declaring a: Bool");
        solver
            .declare_const("b", "Bool")
            .expect("declaring b: Bool");
        solver.assert("(and a (not b))").expect("assertion");
        let is_sat = solver.check_sat().expect("check-sat");
        assert!(is_sat);

        let values = solver.get_model().expect("get-model");
        assert_eq!(
            format!("{:?}", values),
            r#"[("a", [], "Bool", true), ("b", [], "Bool", false)]"#
        );

        let values = solver.get_values(&["a", "b", "(and a (not b))"]);
        match values {
            Ok(values) => assert_eq!(
                format!("{:?}", values),
                r#"[("a", true), ("b", false), ("(and a (not b))", true)]"#
            ),
            Err(e) => assert_eq!(
                &e.to_ml_string(),
                "- some versions of CVC4 produce errors on `get-value` commands, \
                 consider using `get-model` instead\n\
                 - parse error: expected `(` on `eof`"
            ),
        }
    }
}

#[cfg(test)]
pub mod z3 {
    use super::*;
    #[test]
    fn set_logic() {
        let conf = SmtConf::z3();
        let mut solver = Solver::new(conf, Parser).expect("solver creation");
        solver
            .set_logic(::rsmt2::Logic::QF_UF)
            .expect("setting logic");
    }

    #[test]
    fn scenario_1() {
        let mut conf = SmtConf::z3();
        conf.models();
        let mut solver = Solver::new(conf, Parser).expect("solver creation");
        solver
            .declare_const("a", "Bool")
            .expect("declaring a: Bool");
        solver
            .declare_const("b", "Bool")
            .expect("declaring b: Bool");
        solver.assert("(and a (not b))").expect("assertion");
        let is_sat = solver.check_sat().expect("check-sat");
        assert!(is_sat);

        let model = solver.get_model().expect("get-model");
        assert_eq!(
            format!("{:?}", model),
            r#"[("a", [], "Bool", true), ("b", [], "Bool", false)]"#
        );

        let values = solver
            .get_values(&["a", "b", "(and a (not b))"])
            .expect("get-value");

        assert_eq!(
            format!("{:?}", values),
            r#"[("a", true), ("b", false), ("(and a (not b))", true)]"#
        );
    }
}

#[test]
fn logic() {
    let conf = SmtConf::z3();

    let mut solver = Solver::new(conf, ()).expect("solver");

    solver.set_logic(Logic::QF_UF).expect("QF_UF");
    solver.reset().expect("reset");
    solver.set_logic(Logic::QF_LIA).expect("QF_LIA");
    solver.reset().expect("reset");
    solver.set_logic(Logic::QF_NIA).expect("QF_NIA");
    solver.reset().expect("reset");
    solver.set_logic(Logic::QF_LRA).expect("QF_LRA");
    solver.reset().expect("reset");
    solver.set_logic(Logic::QF_AUFLIA).expect("QF_AUFLIA");
    solver.reset().expect("reset");
    solver.set_logic(Logic::AUFLIA).expect("AUFLIA");
    solver.reset().expect("reset");
    solver.set_logic(Logic::AUFLIRA).expect("AUFLIRA");
    solver.reset().expect("reset");
    solver.set_logic(Logic::AUFNIRA).expect("AUFNIRA");
    solver.reset().expect("reset");
    solver.set_logic(Logic::LRA).expect("LRA");
    solver.reset().expect("reset");
}
