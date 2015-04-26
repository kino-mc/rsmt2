use std::io::Write ;
use std::io ;

pub mod common ;
pub mod solver_traits ;
pub mod driver ;
pub mod solver ;

use common::* ;
use solver_traits::Smt2Print ;
use driver::GenericPrinter ;

struct Ident(& 'static str) ;
impl Printable for Ident {
  fn to_smt2(& self, writer: & mut Write) -> IoResUnit {
    write!(writer, "{}", self.0)
  }
}

struct Test { pub stdout: io::Stdout }
impl Writable for Test {
  fn writer(& mut self) -> & mut Write {
    & mut self.stdout
  }
}
impl GenericPrinter<Ident, Ident, Ident> for Test {
  #[inline]
  fn check_sat_assuming_command(& self) -> & 'static str {
    "check-sat-assuming"
  }
  // fn as_printer(& mut self) -> & mut Smt2Print<Ident,Ident,Ident> {
  //   (self as & mut GenericPrinter<Ident,Ident,Ident>)
  // }
}


fn main() { 
  println!("") ;
  println!("Creating test.") ;
  let mut test = Test { stdout: io::stdout() } ;
  println!("reset:") ;
  test.comment(
    "This is a comment.\nHere is another line.".lines()
  ).unwrap() ;
  test.reset().unwrap() ;
  test.declare_fun(Ident("f"), & [Ident("in1"), Ident("in2")], Ident("out")) ;
  test.define_fun(
    Ident("f"),
    & [ (Ident("a"), Ident("in1")), (Ident("b"), Ident("in2")) ],
    Ident("out"),
    Ident("a + b - 4")
  ) ;
  test.check_sat_assuming(& [Ident("a1"), Ident("a2")]) ;
  println!("") ;
}