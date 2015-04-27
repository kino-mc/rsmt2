use std::io::Write ;

extern crate parser_combinators as pcomb ;

pub mod common ;
pub mod solver_traits ;
pub mod solver ;
pub mod conf ;

use common::* ;
use solver_traits::* ;
use solver::Solver ;


#[derive(Clone, Copy)]
struct Ident(& 'static str) ;
impl Printable for Ident {
  fn to_smt2(& self, writer: & mut Write) -> IoResUnit {
    write!(writer, "{}", self.0)
  }
}



fn main() {
  println!("") ;

  let (a,b) = (Ident("a"), Ident("b")) ;
  let b00l = Ident("bool") ;
  let a_or_b = Ident("(or a b)") ;
  let mut solver = Solver::new_z3().unwrap() ;

  solver.declare_const(a, b00l).unwrap() ;
  solver.declare_const(b, b00l).unwrap() ;
  solver.assert(a_or_b).unwrap() ;
  solver.check_sat().unwrap() ;
  solver.get_model().unwrap() ;
  solver.exit().unwrap() ;

  println!("Error:") ;
  for line in solver.err_as_string().unwrap().lines() {
    println!("  {}", line) ;
  } ;
  println!("Output:") ;
  for line in solver.out_as_string().unwrap().lines() {
    println!("  {}", line) ;
  } ;
  println!("") ;
}