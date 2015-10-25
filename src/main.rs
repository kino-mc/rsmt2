// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#[macro_use]
extern crate regex ;
#[macro_use]
extern crate nom ;

use std::str::FromStr ;
use std::io::Write ;
use std::str ;

use nom::{IResult,digit,multispace};
use nom::IResult::*;

use SExpr::* ;
use Var::* ;

mod common ;
mod conf ;
mod parse ;
mod solver ;

use common::* ;

#[derive(Debug,Clone,Copy)]
struct Offset(usize,usize) ;

type Sym = String ;

#[derive(Debug,Clone)]
enum Var {
  Const(Sym),
  SVar0(Sym),
  SVar1(Sym),
}

#[derive(Debug,Clone)]
struct Symbol(Var, Offset) ;

impl SymPrintSmt2 for Symbol {
  fn sym_to_smt2(& self, writer: & mut Write) -> IoResUnit {
    match * self {
      Symbol( Const(ref sym), _) => write!(
        writer, "|{}|", sym
      ),
      Symbol( SVar0(ref sym), ref off) => write!(
        writer, "|{}@{}|", sym, off.0
      ),
      Symbol( SVar1(ref sym), ref off) => write!(
        writer, "|{}@{}|", sym, off.1
      ),
    }
  }
}

#[derive(Debug,Clone)]
enum SExpr {
  Id(Var),
  BConst(bool),
  IConst(usize),
  RConst(usize,usize),
  Lambda(String, Vec<SExpr>),
}

impl SExpr {
  fn unroll(& self, off: Offset) -> Unrolled {
    Unrolled(self, off)
  }
  fn to_smt2(& self, writer: & mut Write, offset: Offset) -> IoResUnit {
    match * self {
      Id(ref var) => match * var {
        Var::Const(ref s) => write!(writer, "|{}|", s),
        Var::SVar0(ref s) => write!(writer, "|{}@{}|", s, offset.0),
        Var::SVar1(ref s) => write!(writer, "|{}@{}|", s, offset.1),
      },
      BConst(ref b) => write!(writer, "{}", b),
      IConst(ref i) => write!(writer, "{}", i),
      RConst(ref n, ref d) => write!(writer, "(/ {} {})", n, d),
      Lambda(ref sym, ref args) => {
        try!( write!(writer, "({}", sym) ) ;
        for arg in args {
          try!( arg.to_smt2(writer, offset) )
        } ;
        write!(writer, ")")
      },
    }
  }
}

struct Unrolled<'a>(& 'a SExpr, Offset) ;

impl<'a> ExprPrintSmt2 for Unrolled<'a> {
  fn expr_to_smt2(& self, writer: & mut Write) -> IoResUnit {
    self.0.to_smt2(writer, self.1)
  }
}


named!{ var<SExpr>,
  chain!(
    tag!("|") ~
    id: is_not!("@|") ~
    int: opt!(
      preceded!(
        char!('@'),
        alt!( char!('0') | char!('1') )
      )
    ) ~
    tag!("|"),
    || match int {
      None => Id(
        Const( str::from_utf8(id).unwrap().to_string() )
      ),
      Some('0') => Id(
        SVar0( str::from_utf8(id).unwrap().to_string() )
      ),
      Some('1') => Id(
        SVar1( str::from_utf8(id).unwrap().to_string() )
      ),
      _ => unreachable!(),
    }
  )
}

named!{ b_const<SExpr>,
  map_res!(
    alt!( tag!("true") | tag!("false") ),
    |s| match FromStr::from_str(str::from_utf8(s).unwrap()) {
      Err(e) => Err(e),
      Ok(b) => Ok(BConst(b)),
    }
  )
}

named!{ i_const<SExpr>,
  map_res!(
    map_res!(digit, str::from_utf8),
    |s| match FromStr::from_str(s) {
      Err(e) => Err(e),
      Ok(i) => Ok(IConst(i)),
    }
  )
}

named!{ r_const<SExpr>,
  chain!(
    tag!("(") ~
    opt!(multispace) ~
    tag!("/") ~
    multispace ~
    lhs: digit ~
    multispace ~
    rhs: digit ~
    opt!(multispace) ~
    tag!(")"),
    || RConst(
      FromStr::from_str(str::from_utf8(lhs).unwrap()).unwrap(),
      FromStr::from_str(str::from_utf8(rhs).unwrap()).unwrap()
    )
  )
}

named!{ lambda<SExpr>,
  chain!(
    tag!("(") ~
    opt!(multispace) ~
    sym: alt!(
      tag!("*") | tag!("/")
    ) ~
    multispace ~
    args: separated_list!(
      multispace, sexpr
    ) ~
    opt!(multispace) ~
    tag!(")"),
    || Lambda(
      FromStr::from_str(str::from_utf8(sym).unwrap()).unwrap(),
      args
    )
  )
}

named!{ sexpr<SExpr>,
  alt!(
    i_const | r_const | b_const | var | lambda |
    delimited!(
      char!('('),
      delimited!(
        opt!(multispace),
        sexpr,
        opt!(multispace)
      ),
      char!(')')
    )
  )
}

named!{ top_sexpr<SExpr>,
  delimited!(
    opt!(multispace),
    sexpr,
    opt!(multispace)
  )
}

struct Parser ;
impl ParseSmt2 for Parser {
  type Ident = SExpr ;
  type Value = SExpr ;
  type Expr = SExpr ;
  type Proof = () ;
  fn parse_ident<'a>(
    & self, array: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], Self::Ident> {
    top_sexpr(array)
  }
  fn parse_value<'a>(
    & self, array: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], SExpr> {
    top_sexpr(array)
  }
  fn parse_expr<'a>(
    & self, array: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], SExpr> {
    top_sexpr(array)
  }
  fn parse_proof<'a>(& self, _: & 'a [u8]) -> IResult<'a, & 'a [u8], Self::Proof> {
    panic!("parser on () called")
  }
}

fn print_parse_result<'a, I>(res: IResult<'a, I, SExpr>) {
  match res {
    Done(_,b) => println!("> {:?}", b),
    Error(e) => println!("> error | {:?}", e),
    Incomplete(n) => println!("> incomplete | {:?}", n),
  } ;
  println!("")
}


pub fn run_parser() {
  let bool_str = b"false" ;
  println!("sexpr(\"{}\")", str::from_utf8(bool_str).unwrap()) ;
  print_parse_result(top_sexpr(bool_str)) ;

  let int_str = b"742" ;
  println!("sexpr(\"{}\")", str::from_utf8(int_str).unwrap()) ;
  print_parse_result(top_sexpr(int_str)) ;

  let rat_str = b"(/ 742 5)" ;
  println!("sexpr(\"{}\")", str::from_utf8(rat_str).unwrap()) ;
  print_parse_result(top_sexpr(rat_str)) ;

  let var_str = b"|a fucking identifier|" ;
  println!("sexpr(\"{}\")", str::from_utf8(var_str).unwrap()) ;
  print_parse_result(top_sexpr(var_str)) ;

  let var_str = b"(|a fucking identifier|)" ;
  println!("sexpr(\"{}\")", str::from_utf8(var_str).unwrap()) ;
  print_parse_result(top_sexpr(var_str)) ;

  let svar_str = b"|a fucking state var @0|" ;
  println!("sexpr(\"{}\")", str::from_utf8(svar_str).unwrap()) ;
  print_parse_result(top_sexpr(svar_str)) ;

  let svar_str = b"|a fucking state var @1|" ;
  println!("sexpr(\"{}\")", str::from_utf8(svar_str).unwrap()) ;
  print_parse_result(top_sexpr(svar_str)) ;

  let expr_str = b"(* |svar  @1| 7 (/ 7 352))" ;
  println!("sexpr(\"{}\")", str::from_utf8(expr_str).unwrap()) ;
  print_parse_result(top_sexpr(expr_str)) ;

  let expr_str = b"( (* |svar  @1| 7 (/ 7 352))      )" ;
  println!("sexpr(\"{}\")", str::from_utf8(expr_str).unwrap()) ;
  print_parse_result(top_sexpr(expr_str)) ;

  ()
}


pub fn run_parser_file() {
  use std::io::{BufReader} ;
  use std::fs::File ;
  use std::path::Path ;

  use nom::{ReadProducer, Stepper} ;
  use nom::StepperState::* ;

  let path = Path::new("rsc/test") ;
  let f = File::open(path).unwrap() ;
  let reader = BufReader::new(f) ;
  let rp = ReadProducer::new(reader, 1000) ;
  let mut stepper = Stepper::new(rp) ;

  loop {
    match stepper.step(top_sexpr) {
      Value(expr) => println!("| {:?}", expr),
      step => { println!("\\ {:?}", step) ; break }
    }
  } ;

  ()
}

pub fn run_solver() {
  use ::conf::* ;
  use ::solver::* ;
  use ::solver::sync::* ;
  use std::process::Command ;

  let conf = SolverConf::z3() ;
  let cmd = Command::new("z3") ;

  let mut solver = match Solver::mk(cmd, conf, Parser) {
    Ok(solver) => solver,
    Err(e) => panic!("{:?}", e),
  } ;

  let v1 = Const("v 1".to_string()) ;
  let sv = "s v".to_string() ;
  let sv_at_0 = SVar0(sv) ;
  let lambda1 = Lambda(
    "and".to_string(), vec![Id(v1.clone()), Id(sv_at_0.clone())]
  ) ;
  let lambda2 = Lambda(
    "not".to_string(), vec![Id(sv_at_0.clone())]
  ) ;
  let offset1 = Offset(0,1) ;
  let offset2 = Offset(1,0) ;

  println!("declaring {:?}", v1) ;
  solver.declare_fun(
    & Symbol(v1.clone(), offset1), &[], "bool"
  ).unwrap() ;
  println!("declaring {:?}, offset is {:?}", sv_at_0, offset1) ;
  solver.declare_fun(
    & Symbol(sv_at_0.clone(), offset1), &[], "bool"
  ).unwrap() ;
  println!("") ;

  println!("asserting {:?}, offset is {:?}", lambda1, offset1) ;
  solver.assert(& lambda1.unroll(offset1)).unwrap() ;
  println!("") ;

  println!("check-sat") ;
  match solver.check_sat() {
    Ok(true) => println!("sat"),
    Ok(false) => println!("unsat"),
    Err(e) => println!("error: {:?}", e),
  } ;
  println!("") ;

  println!("declaring {:?}, offset is {:?}", sv_at_0, offset2) ;
  solver.declare_fun(
    & Symbol(sv_at_0.clone(), offset2), &[], "bool"
  ).unwrap() ;
  println!("") ;

  println!("asserting {:?}, offset is {:?}", lambda2, offset2) ;
  solver.assert(& lambda2.unroll(offset2)).unwrap() ;
  println!("") ;

  println!("check-sat") ;
  match solver.check_sat() {
    Ok(true) => println!("sat"),
    Ok(false) => println!("unsat"),
    Err(e) => println!("error: {:?}", e),
  } ;
  println!("") ;

  println!("get_value") ;
  match solver.get_values(
    & [ Id(sv_at_0.clone()).unroll(offset1) ]
  ) {
    Ok(values) => {
      for (e,v) in values.into_iter() {
        println!("  {:?} = {:?}", e, v)
      }
    },
    Err(e) => println!("error: {:?}", e),
  } ;
  println!("") ;

  println!("get_model") ;
  match solver.get_model() {
    Ok(model) => {
      for (id,v) in model.into_iter() {
        println!("  {:?} = {:?}", id, v)
      }
    },
    Err(e) => println!("error: {:?}", e),
  } ;
  println!("") ;

  println!("asserting {:?}, offset is {:?}", lambda2, offset1) ;
  solver.assert(& lambda2.unroll(offset1)).unwrap() ;
  println!("") ;

  println!("check-sat") ;
  match solver.check_sat() {
    Ok(true) => println!("sat"),
    Ok(false) => println!("unsat"),
    Err(e) => println!("error: {:?}", e),
  } ;

  solver.kill().unwrap() ;

  ()
}


fn main() {
  println!("\n|===| Testing parser.") ;

  run_parser() ;

  println!("\n|===| Testing parser on a file.") ;

  run_parser_file() ;

  println!("\n|===| Testing solver.") ;

  run_solver() ;

  println!("\n") ;

  ()
}



