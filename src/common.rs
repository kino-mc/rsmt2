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

/// Writes a string.
#[inline(always)]
pub fn write_str(
  w: & mut io::Write, s: & str
) -> Res<()> {
  w.write_all( s.as_bytes() ) ? ;
  Ok(())
}

impl<'a, T> Sym2Smt<T> for & 'a str {
  fn sym_to_smt2<Writer>(
    & self, writer: & mut Writer, _: & T
  ) -> Res<()> where Writer: io::Write {
    write_str(writer, self)
  }
}
impl<'a, T> Expr2Smt<T> for & 'a str {
  fn expr_to_smt2<Writer>(
    & self, writer: & mut Writer, _: & T
  ) -> Res<()> where Writer: io::Write {
    write_str(writer, self)
  }
}
impl<'a> Sort2Smt for & 'a str {
  fn sort_to_smt2<Writer>(
    & self, writer: & mut Writer
  ) -> Res<()> where Writer: io::Write {
    write_str(writer, self)
  }
}

impl<T> Sym2Smt<T>  for String {
  fn sym_to_smt2<Writer>(
    & self, writer: & mut Writer, _: & T
  ) -> Res<()> where Writer: io::Write {
    write_str(writer, self)
  }
}
impl<T> Expr2Smt<T> for String {
  fn expr_to_smt2<Writer>(
    & self, writer: & mut Writer, _: & T
  ) -> Res<()> where Writer: io::Write {
    write_str(writer, self)
  }
}
impl Sort2Smt for String {
  fn sort_to_smt2<Writer>(
    & self, writer: & mut Writer
  ) -> Res<()> where Writer: io::Write {
    write_str(writer, self)
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
    write!(writer, "{}", self) ? ;
    Ok(())
  }
}