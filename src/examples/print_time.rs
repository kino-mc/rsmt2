//! A more involved example.
//!
//! This example showcases print-time user-specified information but lacks a proper discussion,
//! because no one has asked for it yet.

// Parser library.
use std::io::Write;

use crate::{parse::*, print::*};

#[cfg(test)]
use crate::examples::get_solver;

use self::Var::*;

/// A type.
#[derive(Debug, Clone, Copy, PartialEq)]
enum Type {
    /// Integers.
    Int,
    /// Booleans.
    Bool,
    /// Reals.
    Real,
}
impl Type {
    /// String representation.
    pub fn to_str(self) -> &'static str {
        match self {
            Type::Int => "Int",
            Type::Bool => "Bool",
            Type::Real => "Real",
        }
    }
}
impl Sort2Smt for Type {
    fn sort_to_smt2<Writer: Write>(&self, writer: &mut Writer) -> SmtRes<()> {
        writer.write_all(self.to_str().as_bytes())?;
        Ok(())
    }
}

/// A symbol is a variable and an offset.
#[derive(Debug, Clone, PartialEq)]
pub struct Symbol<'a, 'b>(&'a Var, &'b Offset);

/// An offset gives the index of current and next step.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Offset(usize, usize);
impl Offset {
    /// Index of the current state.
    #[inline(always)]
    pub fn curr(&self) -> usize {
        self.0
    }
    /// Index of the next state.
    #[inline(always)]
    pub fn next(&self) -> usize {
        self.1
    }
}

/// An unrolled version of something.
#[derive(Debug, Clone, PartialEq)]
pub struct Unrolled<'a, T>(T, &'a Offset);

/// Under the hood a symbol is a string.
pub type Sym = String;

/// A variable wraps a symbol.
#[derive(Debug, Clone, PartialEq)]
pub enum Var {
    /// Variable constant in time (Non-Stateful Var: NSVar).
    NSVar(Sym),
    /// State variable in the current step.
    SVar0(Sym),
    /// State variable in the next step.
    SVar1(Sym),
}
impl Var {
    /// Symbol of a variable.
    pub fn sym(&self) -> &str {
        match *self {
            NSVar(ref s) => s,
            SVar0(ref s) => s,
            SVar1(ref s) => s,
        }
    }
    /// Non-stateful variable constructor.
    pub fn nsvar(s: &str) -> Self {
        NSVar(s.to_string())
    }
    /// State variable in the current step.
    pub fn svar0(s: &str) -> Self {
        SVar0(s.to_string())
    }
    /// State variable in the next step.
    pub fn svar1(s: &str) -> Self {
        SVar1(s.to_string())
    }

    /// Given an offset, an S-expression can be unrolled.
    pub fn unroll<'a, 'b>(&'a self, off: &'b Offset) -> Unrolled<'b, &'a Var> {
        Unrolled(self, off)
    }
}

impl<'a, V: AsRef<Var>> Expr2Smt<()> for Unrolled<'a, V> {
    fn expr_to_smt2<Writer: Write>(&self, writer: &mut Writer, _: ()) -> SmtRes<()> {
        self.0.as_ref().expr_to_smt2(writer, &self.1)
    }
}
impl<'a> Expr2Smt<&'a Offset> for Var {
    fn expr_to_smt2<Writer: Write>(&self, writer: &mut Writer, off: &'a Offset) -> SmtRes<()> {
        match *self {
            NSVar(ref sym) => write!(writer, "|{}|", sym)?,
            // SVar at 0, we use the index of the current step.
            SVar0(ref sym) => write!(writer, "|{}@{}|", sym, off.0)?,
            // SVar at 1, we use the index of the next step.
            SVar1(ref sym) => write!(writer, "|{}@{}|", sym, off.1)?,
        }
        Ok(())
    }
}

impl<'a> Sym2Smt<&'a Offset> for Var {
    fn sym_to_smt2<Writer: Write>(&self, writer: &mut Writer, off: &'a Offset) -> SmtRes<()> {
        self.expr_to_smt2(writer, off)
    }
}
impl<'a, 'b> Sym2Smt<()> for Unrolled<'a, &'b Var> {
    fn sym_to_smt2<Writer: Write>(&self, writer: &mut Writer, _: ()) -> SmtRes<()> {
        self.0.expr_to_smt2(writer, &self.1)
    }
}

/// A constant.
#[derive(Debug, Clone, PartialEq)]
pub enum Const {
    /// Boolean constant.
    BConst(bool),
    /// Integer constant.
    IConst(isize),
    /// Rational constant.
    RConst(isize, usize),
}

impl Expr2Smt<()> for Const {
    fn expr_to_smt2<Writer: Write>(&self, writer: &mut Writer, _: ()) -> SmtRes<()> {
        match *self {
            Const::BConst(b) => write!(writer, "{}", b)?,
            Const::IConst(i) => {
                let neg = i < 0;
                if neg {
                    write!(writer, "(- ")?
                }
                write!(writer, "{}", i.abs())?;
                if neg {
                    write!(writer, ")")?
                }
            }
            Const::RConst(num, den) => {
                let neg = num < 0;
                if neg {
                    write!(writer, "(- ")?
                }
                write!(writer, "(/ {} {})", num, den)?;
                if neg {
                    write!(writer, ")")?
                }
            }
        }
        Ok(())
    }
}

/// An S-expression.
#[derive(Debug, Clone, PartialEq)]
pub enum SExpr {
    /// A variable.
    Id(Var),
    /// A constant.
    Val(Const),
    /// An application of function symbol.
    App(Sym, Vec<SExpr>),
}

impl SExpr {
    /// Application constructor.
    pub fn app(sym: &str, args: Vec<SExpr>) -> Self {
        SExpr::App(sym.to_string(), args)
    }
    /// Given an offset, an S-expression can be unrolled.
    pub fn unroll<'a, 'b>(&'a self, off: &'b Offset) -> Unrolled<'b, &'a SExpr> {
        Unrolled(self, off)
    }
}

impl<'a> Expr2Smt<&'a Offset> for SExpr {
    fn expr_to_smt2<Writer: Write>(&self, writer: &mut Writer, off: &'a Offset) -> SmtRes<()> {
        match *self {
            SExpr::Id(ref var) => var.expr_to_smt2(writer, off),
            SExpr::Val(ref cst) => cst.expr_to_smt2(writer, ()),
            SExpr::App(ref sym, ref args) => {
                write!(writer, "({}", sym)?;
                for arg in args {
                    write!(writer, " ")?;
                    arg.expr_to_smt2(writer, off)?
                }
                write!(writer, ")")?;
                Ok(())
            }
        }
    }
}

impl<'a, 'b> Expr2Smt<()> for Unrolled<'a, &'b SExpr> {
    fn expr_to_smt2<Writer: Write>(&self, writer: &mut Writer, _: ()) -> SmtRes<()> {
        self.0.expr_to_smt2(writer, &self.1)
    }
}

/// Empty parser structure.
#[derive(Clone, Copy)]
pub struct Parser;

impl<'a> IdentParser<(Var, Option<usize>), Type, &'a str> for Parser {
    fn parse_ident(self, s: &'a str) -> SmtRes<(Var, Option<usize>)> {
        if s.len() <= 2 {
            bail!("not one of my idents...")
        }
        let s = &s[1..(s.len() - 1)]; // Removing surrounding pipes.
        let mut parts = s.split('@');
        let id = if let Some(id) = parts.next() {
            id.to_string()
        } else {
            bail!("nothing between my pipes!")
        };
        if let Some(index) = parts.next() {
            use std::str::FromStr;
            Ok((
                Var::SVar0(id),
                match usize::from_str(index) {
                    Ok(index) => Some(index),
                    Err(e) => bail!("while parsing the offset in `{}`: {}", s, e),
                },
            ))
        } else {
            Ok((Var::NSVar(id), None))
        }
    }
    fn parse_type(self, s: &'a str) -> SmtRes<Type> {
        match s {
            "Int" => Ok(Type::Int),
            "Bool" => Ok(Type::Bool),
            "Real" => Ok(Type::Real),
            _ => bail!(format!("unknown type `{}`", s)),
        }
    }
}

impl<'a, Br> ModelParser<(Var, Option<usize>), Type, Const, &'a mut SmtParser<Br>> for Parser
where
    Br: ::std::io::BufRead,
{
    fn parse_value(
        self,
        input: &'a mut SmtParser<Br>,
        _: &(Var, Option<usize>),
        _: &[((Var, Option<usize>), Type)],
        _: &Type,
    ) -> SmtRes<Const> {
        use std::str::FromStr;
        if let Some(b) = input.try_bool()? {
            Ok(Const::BConst(b))
        } else if let Some(int) = input.try_int(|int, pos| match isize::from_str(int) {
            Ok(int) => {
                if pos {
                    Ok(int)
                } else {
                    Ok(-int)
                }
            }
            Err(e) => Err(e),
        })? {
            Ok(Const::IConst(int))
        } else if let Some((num, den)) =
            input.try_rat(
                |num, den, pos| match (isize::from_str(num), usize::from_str(den)) {
                    (Ok(num), Ok(den)) => {
                        if pos {
                            Ok((num, den))
                        } else {
                            Ok((-num, den))
                        }
                    }
                    (Err(e), _) | (_, Err(e)) => Err(format!("{}", e)),
                },
            )?
        {
            Ok(Const::RConst(num, den))
        } else {
            input.fail_with("unexpected value")
        }
    }
}

#[test]
fn declare_non_nullary_fun() {
    let mut solver = get_solver(Parser);

    smtry!(
      solver.declare_fun(
        "my_fun", & [ "Int", "Real", "Bool" ], "Real"
      ), failwith "during function declaration: {:?}"
    );

    solver.kill().expect("kill")
}

#[test]
fn test_native() {
    use self::SExpr::*;

    let mut solver = get_solver(Parser);

    let nsv_0 = Var::nsvar("non-stateful var");
    let s_nsv_0 = Id(nsv_0.clone());
    let nsv_1 = Var::nsvar("also non-stateful");
    let s_nsv_1 = Id(nsv_1.clone());
    let sv_0 = Var::svar0("stateful var");
    let s_sv_0 = Id(sv_0.clone());
    let sv_1 = Var::svar1("also stateful");
    let s_sv_1 = Id(sv_1.clone());
    let app1 = SExpr::app("not", vec![s_sv_0.clone()]);
    let app2 = SExpr::app(">", vec![s_sv_1.clone(), Val(Const::IConst(7))]);
    let app3 = SExpr::app(
        "=",
        vec![
            Val(Const::RConst(-7, 3)),
            SExpr::app("+", vec![s_nsv_1.clone(), Val(Const::RConst(2, 1))]),
        ],
    );
    let app = SExpr::app("and", vec![s_nsv_0.clone(), app1, app2, app3]);
    let offset1 = Offset(0, 1);

    smtry!(
      solver.declare_const_with(& nsv_0, & "Bool", & offset1),
      failwith "declaration failed: {:?}"
    );

    smtry!(
      solver.declare_const_with(& nsv_1, & "Real", & offset1),
      failwith "declaration failed: {:?}"
    );

    smtry!(
      solver.declare_const_with(& sv_0, & "Bool", & offset1),
      failwith "declaration failed: {:?}"
    );

    smtry!(
      solver.declare_const_with(& sv_1, & "Int", & offset1),
      failwith "declaration failed: {:?}"
    );

    smtry!(
      solver.assert_with(& app, & offset1),
      failwith "assert failed: {:?}"
    );

    assert!(smtry!(
      solver.check_sat(),
      failwith "error in checksat: {:?}"
    ));

    let model = smtry!(
      solver.get_model(),
      failwith "while getting model: {:?}"
    );

    for ((var, off), _, typ, val) in model {
        if var.sym() == "stateful var" {
            assert_eq!(off, Some(0));
            assert_eq!(typ, Type::Bool);
            assert_eq!(val, Const::BConst(false))
        } else if var.sym() == "also stateful" {
            assert_eq!(off, Some(1));
            assert_eq!(typ, Type::Int);
            if let Const::IConst(val) = val {
                assert!(val > 7)
            } else {
                panic!("expected variable, got {:?}", val)
            }
        } else if var.sym() == "non-stateful var" {
            assert_eq!(off, None);
            assert_eq!(typ, Type::Bool);
            assert_eq!(val, Const::BConst(true))
        } else if var.sym() == "also non-stateful" {
            assert_eq!(off, None);
            assert_eq!(typ, Type::Real);
            if let Const::RConst(num, den) = val {
                assert_eq!(num * 3 + (2 * 3 * den as isize), (7 * den as isize))
            } else {
                panic!("expected variable, got {:?}", val)
            }
        }
    }

    solver.kill().expect("kill")
}

#[test]
fn test_unroll() {
    use self::SExpr::*;

    let mut solver = get_solver(Parser);

    let nsv_0 = Var::nsvar("non-stateful var");
    let s_nsv_0 = Id(nsv_0.clone());
    let nsv_1 = Var::nsvar("also non-stateful");
    let s_nsv_1 = Id(nsv_1.clone());
    let sv_0 = Var::svar0("stateful var");
    let s_sv_0 = Id(sv_0.clone());
    let sv_1 = Var::svar1("also stateful");
    let s_sv_1 = Id(sv_1.clone());
    let app1 = SExpr::app("not", vec![s_sv_0.clone()]);
    let app2 = SExpr::app(">", vec![s_sv_1.clone(), Val(Const::IConst(7))]);
    let app3 = SExpr::app(
        "=",
        vec![
            Val(Const::RConst(-7, 3)),
            SExpr::app("+", vec![s_nsv_1.clone(), Val(Const::RConst(2, 1))]),
        ],
    );
    let app = SExpr::app("and", vec![s_nsv_0.clone(), app1, app2, app3]);
    let offset1 = Offset(0, 1);

    let sym = nsv_0.unroll(&offset1);
    smtry!(
      solver.declare_const(& sym, & "Bool"),
      failwith "declaration failed: {:?}"
    );

    let sym = nsv_1.unroll(&offset1);
    smtry!(
      solver.declare_const(& sym, & "Real"),
      failwith "declaration failed: {:?}"
    );

    let sym = sv_0.unroll(&offset1);
    smtry!(
      solver.declare_const(& sym, & "Bool"),
      failwith "declaration failed: {:?}"
    );

    let sym = sv_1.unroll(&offset1);
    smtry!(
      solver.declare_const(& sym, & "Int"),
      failwith "declaration failed: {:?}"
    );

    let expr = app.unroll(&offset1);
    smtry!(
      solver.assert(& expr),
      failwith "assert failed: {:?}"
    );

    assert!(smtry!(
      solver.check_sat(),
      failwith "error in checksat: {:?}"
    ));

    let model = smtry!(
      solver.get_model(),
      failwith "while getting model: {:?}"
    );

    for ((var, off), _, typ, val) in model {
        if var.sym() == "stateful var" {
            assert_eq!(off, Some(0));
            assert_eq!(typ, Type::Bool);
            assert_eq!(val, Const::BConst(false))
        } else if var.sym() == "also stateful" {
            assert_eq!(off, Some(1));
            assert_eq!(typ, Type::Int);
            if let Const::IConst(val) = val {
                assert!(val > 7)
            } else {
                panic!("expected variable, got {:?}", val)
            }
        } else if var.sym() == "non-stateful var" {
            assert_eq!(off, None);
            assert_eq!(typ, Type::Bool);
            assert_eq!(val, Const::BConst(true))
        } else if var.sym() == "also non-stateful" {
            assert_eq!(off, None);
            assert_eq!(typ, Type::Real);
            if let Const::RConst(num, den) = val {
                assert_eq!(num * 3 + (2 * 3 * den as isize), (7 * den as isize))
            } else {
                panic!("expected variable, got {:?}", val)
            }
        }
    }

    solver.kill().expect("kill")
}
