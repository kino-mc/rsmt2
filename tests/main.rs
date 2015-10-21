extern crate rsmt2 ;

use rsmt2::common::* ;

type Ident = String ;
type Value = String ;
type Expr  = String ;
type Proof = () ;


mod common {

  impl Printable<(usize, usize)> for String {
    fn to_smt2(
      & self, writer: & mut Write, offset: (usize,usize)
    ) -> IoResUnit {
      write!(writer, "{}", self)
    }
  }

}