// See the LICENSE files at the top-level directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![allow(dead_code)]

use std::io::Write ;
use std::str::FromStr ;
use std::str ;

use * ;
use to_smt::* ;
use errors::* ;

use self::Var::* ;
use self::Const::* ;
use self::SExpr::* ;

/// Under the hood a symbol is a string.
type Sym = String ;

/// A type.
#[derive(Debug, Clone, Copy, PartialEq)]
enum Type {
  /// Int.
  Int,
  /// Bool.
  Bool,
}

/// A variable wraps a symbol.
#[derive(Debug, Clone, PartialEq)]
enum Var {
  /// Variable constant in time (Non-Stateful Var: SVar).
  NSVar(Sym),
  /// State variable in the current step.
  SVar0(Sym),
  /// State variable in the next step.
  SVar1(Sym),
}

/// A constant.
#[derive(Debug, Clone, PartialEq)]
enum Const {
  /// Boolean constant.
  BConst(bool),
  /// Integer constant.
  IConst(usize),
  /// Rational constant.
  RConst(usize,usize),
}

/// A type.
#[derive(Debug, Clone, PartialEq)]

/// An S-expression.
#[derive(Debug, Clone, PartialEq)]
enum SExpr {
  /// A variable.
  Id(Var),
  /// A constant.
  Val(Const),
  /// An application of function symbol.
  App(Sym, Vec<SExpr>),
}

/// An offset gives the index of current and next step.
#[derive(Debug, Clone, Copy, PartialEq)]
struct Offset(usize, usize) ;

/// A symbol is a variable and an offset.
#[derive(Debug, Clone, PartialEq)]
struct Symbol<'a, 'b>(& 'a Var, & 'b Offset) ;

/// An unrolled SExpr.
#[derive(Debug, Clone, PartialEq)]
struct Unrolled<'a, 'b>(& 'a SExpr, & 'b Offset) ;

impl Var {
  pub fn nsvar(s: & str) -> Self { NSVar(s.to_string()) }
  pub fn svar0(s: & str) -> Self { SVar0(s.to_string()) }
  pub fn svar1(s: & str) -> Self { SVar1(s.to_string()) }
  /// Given an offset, a variable can be printed in SMT Lib 2.
  #[inline(always)]
  pub fn to_smt2<Writer>(
    & self, writer: & mut Writer, off: & Offset
  ) -> Res<()> where Writer: Write {
    match * self {
      NSVar(ref sym) => write!(writer, "|{}|", sym) ?,
      /// SVar at 0, we use the index of the current step.
      SVar0(ref sym) => write!(writer, "|{}@{}|", sym, off.0) ?,
      /// SVar at 1, we use the index of the next step.
      SVar1(ref sym) => write!(writer, "|{}@{}|", sym, off.1) ?,
    }
    Ok(())
  }
  /// Given an offset, a variable can become a Symbol.
  pub fn to_sym<'a, 'b>(& 'a self, off: & 'b Offset) -> Symbol<'a, 'b> {
    Symbol(self, off)
  }
}

impl Const {
  /// A constant can be printed in SMT Lib 2.
  #[inline(always)]
  pub fn to_smt2<Writer>(
    & self, writer: & mut Writer
  ) -> Res<()> where Writer: Write {
    match * self {
      BConst(ref b) => write!(writer, "{}", b) ?,
      IConst(ref i) => write!(writer, "{}", i) ?,
      RConst(ref num, ref den) => write!(writer, "(/ {} {})", num, den) ?,
    }
    Ok(())
  }
}

impl SExpr {
  pub fn app(sym: & str, args: Vec<SExpr>) -> Self {
    App(sym.to_string(), args)
  }
  /// Given an offset, an S-expression can be printed in SMT Lib 2.
  pub fn to_smt2<Writer>(
    & self, writer: & mut Writer, off: & Offset
  ) -> Res<()> where Writer: Write {
    match * self {
      Id(ref var) => var.to_smt2(writer, off),
      Val(ref cst) => cst.to_smt2(writer),
      App(ref sym, ref args) => {
        write!(writer, "({}", sym) ? ;
        for ref arg in args {
          write!(writer, " ") ? ;
          arg.to_smt2(writer, off) ?
        }
        write!(writer, ")") ? ;
        Ok(())
      }
    }
  }
  /// Given an offset, an S-expression can be unrolled.
  pub fn unroll<'a, 'b>(& 'a self, off: & 'b Offset) -> Unrolled<'a,'b> {
    Unrolled(self, off)
  }
}
/// A symbol can be printed in SMT Lib 2.
impl<'a, 'b> Sym2Smt<()> for Symbol<'a,'b> {
  fn sym_to_smt2<Writer>(
    & self, writer: & mut Writer, _: & ()
  ) -> Res<()> where Writer: Write {
    self.0.to_smt2(writer, self.1)
  }
}

/// An unrolled SExpr can be printed in SMT Lib 2.
impl<'a, 'b> Expr2Smt<()> for Unrolled<'a,'b> {
  fn expr_to_smt2<Writer>(
    & self, writer: & mut Writer, _: & ()
  ) -> Res<()> where Writer: Write {
    self.0.to_smt2(writer, self.1)
  }
}

struct NuParser ;
impl IdentParser<Var, Type> for NuParser {
  fn parse_ident(self, input: & str)
}

/// Parser structure for S-expressions.
struct Parser ;
impl ParseSmt2 for Parser {
  type Ident = Var ;
  type Value = Const ;
  type Expr = SExpr ;
  type Proof = () ;
  type I = () ;

  fn parse_ident<'a>(
    & self, array: & 'a [u8]
  ) -> IResult<& 'a [u8], Var> {
    var(array)
  }
  fn parse_value<'a>(
    & self, array: & 'a [u8]
  ) -> IResult<& 'a [u8], Const> {
    cst(array)
  }
  fn parse_expr<'a>(
    & self, array: & 'a [u8], _ : & ()
  ) -> IResult<& 'a [u8], SExpr> {
    s_expr(array)
  }
  fn parse_proof<'a>(
    & self, _: & 'a [u8]
  ) -> IResult<& 'a [u8], ()> {
    panic!("proof parsing is not supported")
  }
}

/// Convenience macro.
#[allow(unused_macros)]
macro_rules! smtry {
  ($e:expr, failwith $( $msg:expr ),+) => (
    match $e {
      Ok(something) => something,
      Err(e) => panic!( $($msg),+ , e)
    }
  ) ;
}

#[test]
fn test() {
  use conf::* ;

  let conf = SolverConf::z3() ;

  let mut kid = match Kid::new(conf) {
    Ok(kid) => kid,
    Err(e) => panic!("Could not spawn solver kid: {:?}", e)
  } ;

  {

    let mut solver = smtry!(
      solver(& mut kid, Parser),
      failwith "could not create solver: {:?}"
    ) ;

    let nsv = Var::nsvar("non stateful var") ;
    let s_nsv = Id(nsv.clone()) ;
    let sv_0 = Var::svar0("stateful var") ;
    let s_sv_0 = Id(sv_0.clone()) ;
    let app2 = SExpr::app("not", vec![ s_sv_0.clone() ]) ;
    let app1 = SExpr::app("and", vec![ s_nsv.clone(), app2.clone() ]) ;
    let offset1 = Offset(0,1) ;

    let sym = nsv.to_sym(& offset1) ;
    smtry!(
      solver.declare_fun(& sym, &[] as & [& str], & "bool", & ()),
      failwith "declaration failed: {:?}"
    ) ;

    let sym = sv_0.to_sym(& offset1) ;
    smtry!(
      solver.declare_fun(& sym, &[] as & [& str], & "bool", & ()),
      failwith "declaration failed: {:?}"
    ) ;

    let expr = app1.unroll(& offset1) ;
    smtry!(
      solver.assert(& expr, & ()),
      failwith "assert failed: {:?}"
    ) ;

    match smtry!(
      solver.check_sat(),
      failwith "error in checksat: {:?}"
    ) {
      true => println!("> sat"),
      false => panic!("expected sat, got unsat"),
    } ;

    let model = smtry!(
      solver.get_model(),
      failwith "could not retrieve model: {:?}"
    ) ;
    for (id,v) in model.into_iter() {
      let res = if id == sv_0 {
        BConst(false)
      } else {
        if id == nsv { BConst(true) } else {
          panic!("expected {:?} or {:?}, got {:?}", sv_0, nsv, id)
        }
      } ;
      if v != res {
        panic!("expected {:?} for {:?}, got {:?}", res, id, v)
      }
    } ;

    let values = smtry!(
      solver.get_values(
        & [ app1.unroll(& offset1), app2.unroll(& offset1)], & ()
      ),
      failwith "error in get-values: {:?}"
    ) ;
    for (e,v) in values.into_iter() {
      let res = if e == app1 || e == app2 { BConst(true) } else {
        panic!("expected {:?} or {:?}, got {:?}", app1, app2, e)
      } ;
      if v != res {
        panic!("expected {:?} for {:?}, got {:?}", res, e, v)
      }
    }

  }

  smtry!(
    kid.kill(),
    failwith "error while killing solver: {:?}"
  )
}