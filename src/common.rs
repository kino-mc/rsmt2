// See the LICENSE files at the top-level directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Basic types used by the library.

use std::io ;
use std::fmt ;

use nom::IResult ;

use errors::* ;


/// A symbol printable in the SMT Lib 2 standard given some info.
pub trait Sym2Smt<Info> {
  /// Prints a symbol to a writer given some info.
  fn sym_to_smt2<Writer>(& self, & mut Writer, & Info) -> Res<()>
  where Writer: io::Write ;
}

/// An expression printable in the SMT Lib 2 standard given some info.
pub trait Expr2Smt<Info> {
  /// Prints an expression to a writer given some info.
  fn expr_to_smt2<Writer>(& self, & mut Writer, & Info) -> Res<()>
  where Writer: io::Write ;
}

/// A sort printable in the SMT Lib 2 standard.
pub trait Sort2Smt {
  /// Prints a sort to a writer info.
  fn sort_to_smt2<Writer>(& self, & mut Writer) -> Res<()>
  where Writer: io::Write ;
}

/// Prints a string as a symbol.
fn write(
  s: & str, w: & mut io::Write, info_1: & str, info_2: & str
) -> Res<()> {
  write!(w, "{}", s).chain_err(
    || ErrorKind::IoError(
      format!("writing {} as {}", info_1, info_2)
    )
  )
}

impl<'a> Sym2Smt<()>  for & 'a str {
  fn sym_to_smt2<Writer>(
    & self, writer: & mut Writer, _: & ()
  ) -> Res<()> where Writer: io::Write {
    write(self, writer, "& str", "symbol")
  }
}
impl<'a> Expr2Smt<()> for & 'a str {
  fn expr_to_smt2<Writer>(
    & self, writer: & mut Writer, _: & ()
  ) -> Res<()> where Writer: io::Write {
    write(self, writer, "& str", "expression")
  }
}
impl<'a> Sort2Smt for & 'a str {
  fn sort_to_smt2<Writer>(
    & self, writer: & mut Writer
  ) -> Res<()> where Writer: io::Write {
    write(self, writer, "& str", "sort")
  }
}

impl Sym2Smt<()>  for String {
  fn sym_to_smt2<Writer>(
    & self, writer: & mut Writer, _: & ()
  ) -> Res<()> where Writer: io::Write {
    write(self, writer, "String", "symbol")
  }
}
impl Expr2Smt<()> for String {
  fn expr_to_smt2<Writer>(
    & self, writer: & mut Writer, _: & ()
  ) -> Res<()> where Writer: io::Write {
    write(self, writer, "String", "expression")
  }
}
impl Sort2Smt for String {
  fn sort_to_smt2<Writer>(
    & self, writer: & mut Writer
  ) -> Res<()> where Writer: io::Write {
    write(self, writer, "String", "sort")
  }
}



/** Parsers on the user's structure.

Not all of them are necessary depending on the queries wanted. See each method
for details.*/
pub trait ParseSmt2 {
  /// Type of identifiers in the user's structure.
  type Ident : ::std::fmt::Debug ;
  /// Type of values in the user's structure.
  type Value : ::std::fmt::Debug ;
  /// Type of expressions in the user's structure.
  type Expr :  ::std::fmt::Debug ;
  /// Type of proofs in the user's structure.
  type Proof : ::std::fmt::Debug ;
  /// Type of the info passed when parsing expressions.
  type I ;

  /** Parses an ident from self, viewed as a reader.
  
  Required by
  
  * `get-assignment`
  * `get-model`
  * `get-unsat-assumptions`
  * `get-unsat-core` */
  #[inline(always)]
  fn parse_ident<'a>(
    & self, & 'a [u8]
  ) -> IResult<& 'a [u8], Self::Ident> ;

  /** Parses a value from self, viewed as a reader.

  Required by

  * `get-value`
  * `get-assignment`
  * `get-model` */
  #[inline(always)]
  fn parse_value<'a>(
    & self, & 'a [u8]
  ) -> IResult<& 'a [u8], Self::Value> ;

  /** Parses an expression from self, viewed as a reader.

  Required by

  * `get_assertions` */
  #[inline(always)]
  fn parse_expr<'a>(
    & self, & 'a [u8], & Self::I
  ) -> IResult<& 'a [u8], Self::Expr> ;

  /** Parses a proof from self, viewed as a reader.

  Required by

  * `get_proof` */
  #[inline(always)]
  fn parse_proof<'a>(
    & self, & 'a [u8]
  ) -> IResult<& 'a [u8], Self::Proof> ;
}

impl ParseSmt2 for () {
  type Ident = () ;
  type Value = () ;
  type Expr = () ;
  type Proof = () ;
  type I = () ;
  fn parse_ident<'a>(
    & self, _: & 'a [u8]
  ) -> IResult<& 'a [u8], Self::Ident> {
    panic!("parser on () called")
  }
  fn parse_value<'a>(
    & self, _: & 'a [u8]
  ) -> IResult<& 'a [u8], Self::Value> {
    panic!("parser on () called")
  }
  fn parse_expr<'a>(
    & self, _: & 'a [u8], _: & ()
  ) -> IResult<& 'a [u8], Self::Expr> {
    panic!("parser on () called")
  }
  fn parse_proof<'a>(
    & self, _: & 'a [u8]
  ) -> IResult<& 'a [u8], Self::Proof> {
    panic!("parser on () called")
  }
}



/// SMT Lib 2 logics.
#[allow(non_camel_case_types)]
pub enum Logic {
  /// Quantifier-free uninterpreted functions.
  QF_UF,
  /// Quantifier-free linear integer arithmetic.
  QF_LIA,
  /// Quantifier-free non-linear integer arithmetic.
  QF_NIA,
  /// Quantifier-free linear real arithmetic.
  QF_LRA,
  /** Quantifier-free arrays, uninterpreted functions, linear integer
  arithmetic. */
  QF_AUFLIA,
  /** Quantifier-free arrays, uninterpreted functions, linear integer
  arithmetic. */
  AUFLIA,
  /// Arrays, uninterpreted functions, linear integer/real arithmetic.
  AUFLIRA,
  /// arrays, uninterpreted functions, non-linear integer/real arithmetic.
  AUFNIRA,
  /// Linear real arithmetic.
  LRA,
}
impl fmt::Display for Logic {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    use self::Logic::* ;
    match * self {
      QF_UF => write!(fmt, "QF_UF"),
      QF_LIA => write!(fmt, "QF_LIA"),
      QF_NIA => write!(fmt, "QF_NIA"),
      QF_LRA => write!(fmt, "QF_LRA"),
      QF_AUFLIA => write!(fmt, "QF_AUFLIA"),
      AUFLIA => write!(fmt, "AUFLIA"),
      AUFLIRA => write!(fmt, "AUFLIRA"),
      AUFNIRA => write!(fmt, "AUFNIRA"),
      LRA => write!(fmt, "LRA"),
    }
  }
}
impl Logic {
  /// Prints the logic in a writer in SMT Lib 2 format.
  pub fn to_smt2(& self, writer: & mut io::Write, _: ()) -> Res<()> {
    write!(writer, "{}", self).chain_err(
      || ErrorKind::IoError(
        format!("could not write logic '{}'", self)
      )
    )
  }
}