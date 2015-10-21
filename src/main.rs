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

mod common ;

use common::* ;

#[derive(Debug)]
struct SVar { pub id: String }

#[derive(Debug)]
enum SExpr {
  Var(String),
  SVar0(SVar),
  SVar1(SVar),
  BConst(bool),
  IConst(usize),
  RConst(usize,usize),
  Lambda(String, Vec<SExpr>),
}

#[derive(Debug,Clone,Copy)]
struct Offset(usize,usize) ;

impl PrintSmt2<Offset> for SExpr {
  fn to_smt2(& self, writer: & mut Write, offset: Offset) -> IoResUnit {
    match * self {
      Var(ref s) => write!(writer, "|{}|", s),
      SVar0(ref sv) => write!(writer, "|{}@{}|", sv.id, offset.0),
      SVar1(ref sv) => write!(writer, "|{}@{}|", sv.id, offset.1),
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
      None => Var(
        str::from_utf8(id).unwrap().to_string()
      ),
      Some('0') => SVar0(
        SVar {
          id: str::from_utf8(id).unwrap().to_string()
        }
      ),
      Some('1') => SVar1(
        SVar {
          id: str::from_utf8(id).unwrap().to_string()
        }
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

fn print_parse_result<'a, I>(res: IResult<'a, I, SExpr>) {
  match res {
    Done(_,b) => println!("> {:?}", b),
    Error(e) => println!("> error | {:?}", e),
    Incomplete(n) => println!("> incomplete | {:?}", n),
  } ;
  println!("")
}


pub fn run_common() {
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


pub fn run_common_file() {
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


fn main() {
  println!("\n") ;

  run_common() ;

  println!("\n") ;

  run_common_file() ;

  println!("\n") ;

  ()
}



