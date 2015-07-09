use std::io::Write ;

#[macro_use(parser, parse_try)]
extern crate parse_comb ;

// extern crate parser_combinators as pcomb ;

pub mod common ;
// pub mod solver_traits ;
// pub mod solver ;
// pub mod conf ;

use common::* ;
// use solver_traits::* ;
// use solver::Solver ;


// #[derive(Clone, Copy)]
// struct Ident(& 'static str) ;
// impl Printable for Ident {
//   fn to_smt2(& self, writer: & mut Write) -> IoResUnit {
//     write!(writer, "{}", self.0)
//   }
// }



// fn main() {
//   println!("") ;

//   let (a,b) = (Ident("a"), Ident("b")) ;
//   let b00l = Ident("bool") ;
//   let a_or_b = Ident("(or a b)") ;
//   let mut solver = Solver::new_z3().unwrap() ;

//   solver.declare_const(a, b00l).unwrap() ;
//   solver.declare_const(b, b00l).unwrap() ;
//   solver.assert(a_or_b).unwrap() ;
//   solver.check_sat().unwrap() ;
//   solver.get_model().unwrap() ;
//   solver.exit().unwrap() ;

//   println!("Error:") ;
//   for line in solver.err_as_string().unwrap().lines() {
//     println!("  {}", line) ;
//   } ;
//   println!("Output:") ;
//   for line in solver.out_as_string().unwrap().lines() {
//     println!("  {}", line) ;
//   } ;
//   println!("") ;
// }


use parse_comb::{Token, Result} ;
use parse_comb::lexer::LexerCursor ;

// parser!(
//   fn unex_smt_result: UnexSmtResult {
//     | (
//       ["unsupported"] => _ => { UnexSmtResult::Unsupported }
//     )
//     | (
//       ( ( ["("], ["error"], ["\""] )
//         > { r"^[^\x22]*" } <
//         ( ["\""], [")"] ) ) => err => {
//         UnexSmtResult::Error(err.tkn)
//       }
//     )
//   }
// ) ;

// parser!(
//   fn checksat_result: SmtParseResult<bool> {
//     | (unex_smt_result => err => {Err(err)} )
//     | (["sat"] => _ => {Ok(true)} )
//     | (["unsat"] => _ => {Ok(false)} )
//   }
// ) ;

parser!(
  fn ident_parser: Token {
    { r"^[a-zA-Z][a-zA-Z_]*" }
  }
) ;

// parser!(
//   fn bool_parser: bool {
//     | (["false"] => _ => { false })
//     | (["true"] => _ => { true })
//   }
// ) ;

// macro_rules! try_parse {
//   ($e:expr) => (
//     match $e {
//       Result::Ok(res, lexer) => (res, lexer),
//       Result::Err(e) => return Result::Err(e),
//     }
//   )
// }


trait SmtPrinter<Term> {
  fn print_term(& mut self, w: & mut Write, term: & Term) -> IoResUnit ;
  fn assert(& mut self, w: & mut Write, term: & Term) -> IoResUnit {
    try!( write!(w, "(assert ") ) ;
    try!( self.print_term(w, term) ) ;
    write!(w, ")\n")
  }
  fn checksat(& mut self, w: & mut Write) -> IoResUnit {
    write!(w, "(check-sat)\n")
  }
  fn get_model(& mut self, w: & mut Write) -> IoResUnit {
    write!(w, "(get-model)\n")
  }
}

parser!(
  fn define_fun_head: () {
    ["(define-fun"] => _ => { () }
  }
) ;
parser!(
  fn define_fun_tail: () {
    [")"] => _ => { () }
  }
) ;
parser!(
  fn model_head: () {
    ["(model"] => _ => { () }
  }
) ;
parser!(
  fn model_tail: () {
    [")"] => _ => { () }
  }
) ;

trait SmtParser<Term> {
  fn parse_term(& mut self, lexer: & LexerCursor) -> Result<Term> ;

  fn define_fun_parser(
    & mut self, lexer: & LexerCursor
  ) -> Result<(Term,Term)> {
    let (_, lexer) = parse_try!( define_fun_head(& lexer) ) ;
    let (term1, lexer) = parse_try!( self.parse_term(& lexer) ) ;
    let (term2, lexer) = parse_try!( self.parse_term(& lexer) ) ;
    let (_, lexer) = parse_try!( define_fun_tail(& lexer) ) ;
    Result::Ok( (term1, term2), lexer )
  }

  fn get_model_parser(
    & mut self, lexer: & LexerCursor
  ) -> Result<Vec<(Term,Term)>> {
    let (_, lexer) = parse_try!( model_head(& lexer) ) ;
    let mut res = Vec::new() ;
    let mut lexer = lexer ;
    loop {
      match self.define_fun_parser(& lexer) {
        Result::Ok( (var, val), nu_lexer ) => {
          res.push( (var,val) ) ;
          lexer = nu_lexer
        },
        Result::Err(_) => break,
      }
    } ;
    let (_, lexer) = parse_try!( model_tail(& lexer) ) ;
    Result::Ok( res, lexer )
  }
}

struct Dummy ;

impl SmtParser<String> for Dummy {
  fn parse_term(& mut self, lexer: & LexerCursor) -> Result<String> {
    let (tkn, lexer) = parse_try!(ident_parser(lexer)) ;
    Result::Ok(tkn.tkn, lexer)
  }
}

fn main () {
  println!("whatever") ;
  let mut dummy = Dummy ;
  let test_string =
    "(model (define-fun a true ) (define-fun b false ) )".to_string() ;
  let lexer = parse_comb::lexer::Lexer::of_string(
    & test_string, & parse_comb::lexer::simple_is_whitespace
  ) ;
  match dummy.get_model_parser(
    & parse_comb::lexer::LexerCursor::of_lexer(lexer)
  ) {
    Result::Ok(pairs, _) => for (var,val) in pairs {
      println!("> {} = {}", var, val)
    },
    Result::Err(e) => println!("Error: {}", e),
  }
}

