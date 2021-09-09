use crate::{parse::*, *};

type Typ = String;
type Ident = String;
type Expr = String;
type Val = String;

#[derive(Clone, Copy)]
struct Parser;
impl<'a> ValueParser<Val, &'a str> for Parser {
    fn parse_value(self, input: &'a str) -> SmtRes<Val> {
        Ok(input.into())
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
        Ok(input.into())
    }
}

#[cfg(test)]
pub mod cvc4 {
    use super::*;
    #[test]
    fn set_logic() {
        let conf = SmtConf::default_cvc4();
        let mut solver = Solver::new(conf, Parser).expect("solver creation");
        solver.set_logic(Logic::QF_UF).expect("set-logic");
    }

    #[test]
    fn scenario_1() {
        let mut conf = SmtConf::default_cvc4();
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
            r#"[("a", [], "Bool", "true"), ("b", [], "Bool", "false")]"#
        );

        let values = solver.get_values(&["a", "b", "(and a (not b))"]);
        match values {
            Ok(values) => assert_eq!(
                format!("{:?}", values),
                r#"[("a", "true"), ("b", "false"), ("(and a (not b))", "true")]"#
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
        let conf = SmtConf::default_z3();
        let mut solver = Solver::new(conf, Parser).expect("solver creation");
        solver.set_logic(Logic::QF_UF).expect("set-logic");
    }

    #[test]
    fn scenario_1() {
        let mut conf = SmtConf::default_z3();
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
        let model = format!("{:?}", model);
        println!("model: {}", model);
        assert!(
            model == r#"[("b", [], "Bool", "false"), ("a", [], "Bool", "true")]"#
                || model == r#"[("a", [], "Bool", "true"), ("b", [], "Bool", "false")]"#
        );

        let values = solver
            .get_values(&["a", "b", "(and a (not b))"])
            .expect("get-value");

        assert_eq!(
            format!("{:?}", values),
            r#"[("a", "true"), ("b", "false"), ("(and a (not b))", "true")]"#
        );
    }

    #[test]
    fn actlits_0() {
        let mut solver = Solver::default_z3(()).unwrap();
        solver.declare_const("x", "Int").unwrap();

        solver.declare_const("actlit", "Bool").unwrap();
        solver
            .assert(
                "\
                 (=> actlit \
                 (and (> x 0) (< x 3) (= (mod x 3) 0))\
                 )\
                 ",
            )
            .unwrap();
        assert!(!solver.check_sat_assuming(Some("actlit")).unwrap());
        solver.assert("(not actlit)").unwrap();

        solver.declare_const("other_actlit", "Bool").unwrap();
        solver
            .assert(
                "\
                 (=> other_actlit \
                 (and (> x 7) (= (mod x 2) 0))\
                 )\
                 ",
            )
            .unwrap();
        assert!(solver.check_sat_assuming(Some("other_actlit")).unwrap());
        solver.assert("(not other_actlit)").unwrap();

        solver.kill().unwrap()
    }

    #[test]
    fn actlits_1() {
        let mut solver = match Solver::default_z3(()) {
            Ok(kid) => kid,
            Err(e) => panic!("Could not spawn solver kid: {:?}", e),
        };

        solver.declare_const("x", "Int").unwrap();

        let actlit = solver.get_actlit().unwrap();
        solver.assert_act(&actlit, "(> x 0)").unwrap();
        solver.assert_act(&actlit, "(< x 3)").unwrap();
        solver.assert_act(&actlit, "(= (mod x 3) 0)").unwrap();

        assert!(!solver.check_sat_act(Some(&actlit)).unwrap());
        solver.de_actlit(actlit).unwrap();
        // At this point `actlit` has been consumed. So it's a bit safer than the
        // version above, since use-after-deactivate is not possible.

        let actlit = solver.get_actlit().unwrap();
        solver.assert_act(&actlit, "(> x 7)").unwrap();
        solver.assert_act(&actlit, "(= (mod x 2) 0)").unwrap();
        assert!(solver.check_sat_act(Some(&actlit)).unwrap());
        solver.de_actlit(actlit).unwrap();

        solver.kill().unwrap()
    }
}

#[cfg(test)]
pub mod yices_2 {
    use super::*;
    #[test]
    fn set_logic() {
        let conf = SmtConf::default_yices_2();
        let mut solver = Solver::new(conf, Parser).expect("solver creation");
        solver.set_logic(Logic::QF_UF).expect("set-logic");
    }

    #[test]
    fn scenario_1() {
        let conf = SmtConf::default_yices_2();
        let mut solver = Solver::new(conf, Parser).expect("solver creation");

        solver.set_logic(Logic::QF_LIA).expect("set-logic");

        solver
            .declare_const("a", "Bool")
            .expect("declaring a: Bool");
        solver
            .declare_const("b", "Bool")
            .expect("declaring b: Bool");
        solver.assert("(and a (not b))").expect("assertion");
        let is_sat = solver
            .check_sat()
            .map_err(|e| println!("{}", e.to_ml_string()))
            .expect("check-sat");
        assert!(is_sat);

        let values = solver
            .get_values(&["a", "b", "(and a (not b))"])
            .expect("get-value");

        assert_eq!(
            format!("{:?}", values),
            r#"[("a", "true"), ("b", "false"), ("(and a (not b))", "true")]"#
        );

        let model = solver.get_model();
        match model {
            Ok(model) => assert_eq!(
                format!("{:?}", model),
                r#"[("a", [], "Bool", "true"), ("b", [], "Bool", "false")]"#
            ),
            Err(e) => assert_eq!(
                &e.to_ml_string(),
                "- Note: model production is not active for this SmtConf (`conf.models()`)\n\
                 - parse error: expected `model` on `=`"
            ),
        }
    }

    #[test]
    fn actlits_1() {
        let mut conf = SmtConf::default_yices_2();
        conf.incremental();

        let mut solver = match Solver::new(conf, Parser) {
            Ok(kid) => kid,
            Err(e) => panic!("Could not spawn solver kid: {:?}", e),
        };
        solver.set_logic(Logic::QF_LIA).expect("set logic");

        solver.declare_const("x", "Int").expect("declare const");

        let actlit = solver.get_actlit().expect("get actlit");
        let mut buf: Vec<u8> = vec![];
        actlit.write(&mut buf).unwrap();
        assert_eq!("|rsmt2 actlit 0|", ::std::str::from_utf8(&buf).unwrap());

        solver.assert_act(&actlit, "(> x 7)").expect("assert act 1");
        solver
            .assert_act(&actlit, "(= (* x 2) 24)")
            .expect("assert act 2");
        assert!(solver.check_sat_act(Some(&actlit)).expect("check sat act"));

        let model = solver.get_values(&["x"]).expect("get value");

        assert_eq!(format!("{:?}", model), r#"[("x", "12")]"#);

        solver.de_actlit(actlit).unwrap();

        solver.kill().unwrap()
    }
}

#[test]
fn logic() {
    let conf = SmtConf::default_z3();

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
