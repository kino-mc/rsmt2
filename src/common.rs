// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!
Basic types used by the library.
*/

use std::io ;
use std::sync::Arc ;

use nom::IResult ;


/** Alias for `io` results of unit. */
pub type IoResUnit = io::Result<()> ;
/** Alias for `io` results of `bool`. */
pub type IoResBool = io::Result<bool> ;
/** Alias for generic `io` results. */
pub type IoRes<T> = io::Result<T> ;



/** Unexpected result for an SMT Lib 2 command. */
#[derive(Debug)]
pub enum UnexSmtRes {
  /** An unsupported command was issued. */
  Unsupported,
  /** A command produced an error. */
  Error(String),
  /** An input/output error occured. */
  IOError(io::Error),
}

/** Result of an SMT query. */
pub type SmtRes<T> = Result<T, UnexSmtRes> ;

/** Result of an SMT statement. */
pub type UnitSmtRes = SmtRes<()> ;


/** A symbol printable in the SMT Lib 2 standard. */
pub trait Sym2Smt {
  /** Prints a symbol to a writer. */
  fn sym_to_smt2(& self, writer: & mut io::Write) -> IoResUnit ;
}
impl<T: Sym2Smt> Sym2Smt for Arc<T> {
  fn sym_to_smt2(& self, writer: & mut io::Write) -> IoResUnit {
    (* * self).sym_to_smt2(writer)
  }
}
/** A symbol printable in the SMT Lib 2 standard given some info. */
pub trait SymInfo2Smt<Info> {
  /** Prints a symbol to a writer given some info. */
  fn sym_info_to_smt2(
    & self, info: & Info, writer: & mut io::Write
  ) -> IoResUnit ;
}
impl<'a, 'b, Info, T: SymInfo2Smt<Info>> Sym2Smt for (& 'a T, & 'b Info) {
  fn sym_to_smt2(& self, writer: & mut io::Write) -> IoResUnit {
    self.0.sym_info_to_smt2(self.1, writer)
  }
}

/** An expression printable in the SMT Lib 2 standard. */
pub trait Expr2Smt {
  /** Prints an expression to a writer. */
  fn expr_to_smt2(& self, writer: & mut io::Write) -> IoResUnit ;
}
impl<T: Expr2Smt> Expr2Smt for Arc<T> {
  fn expr_to_smt2(& self, writer: & mut io::Write) -> IoResUnit {
    (* * self).expr_to_smt2(writer)
  }
}
/** An expression printable in the SMT Lib 2 standard given some info. */
pub trait ExprInfo2Smt<Info> {
  /** Prints an expression to a writer given some info. */
  fn expr_info_to_smt2(
    & self, info: & Info, writer: & mut io::Write
  ) -> IoResUnit ;
}
impl<'a, 'b, Info, T: ExprInfo2Smt<Info>> Expr2Smt for (& 'a T, & 'b Info) {
  fn expr_to_smt2(& self, writer: & mut io::Write) -> IoResUnit {
    self.0.expr_info_to_smt2(self.1, writer)
  }
}

/** A sort printable in the SMT Lib 2 standard. */
pub trait Sort2Smt {
  /** Prints a sort to a writer. */
  fn sort_to_smt2(& self, writer: & mut io::Write) -> IoResUnit ;
}
impl<T: Sort2Smt> Sort2Smt for Arc<T> {
  fn sort_to_smt2(& self, writer: & mut io::Write) -> IoResUnit {
    (* * self).sort_to_smt2(writer)
  }
}
/** A sort printable in the SMT Lib 2 standard given some info. */
pub trait SortInfo2Smt<Info> {
  /** Prints a sort to a writer given some info. */
  fn sort_info_to_smt2(
    & self, info: & Info, writer: & mut io::Write
  ) -> IoResUnit ;
}
impl<'a, 'b, Info, T: SortInfo2Smt<Info>> Sort2Smt for (& 'a T, & 'b Info) {
  fn sort_to_smt2(& self, writer: & mut io::Write) -> IoResUnit {
    self.0.sort_info_to_smt2(self.1, writer)
  }
}

impl<'a> Sym2Smt  for & 'a str {
  fn sym_to_smt2(& self, writer: & mut io::Write) -> IoResUnit {
    write!(writer, "{}", self)
  }
}
impl<'a> Expr2Smt for & 'a str {
  fn expr_to_smt2(& self, writer: & mut io::Write) -> IoResUnit {
    self.sym_to_smt2(writer)
  }
}
impl<'a> Sort2Smt for & 'a str {
  fn sort_to_smt2(& self, writer: & mut io::Write) -> IoResUnit {
    self.sym_to_smt2(writer)
  }
}



/** Generic type for the parsing of an SMT Lib 2 answer.

Either a value of the expected type or an unexpected error. */
pub type SmtParseResult<T> = Result<T, UnexSmtRes> ;



/** Parsers on the user's structure.

Not all of them are necessary depending on the queries wanted. See each method
for details.*/
pub trait ParseSmt2 {
  /** Type of identifiers in the user's structure. */
  type Ident : ::std::fmt::Debug ;
  /** Type of values in the user's structure. */
  type Value : ::std::fmt::Debug ;
  /** Type of expressions in the user's structure. */
  type Expr :  ::std::fmt::Debug ;
  /** Type of proofs in the user's structure. */
  type Proof : ::std::fmt::Debug ;

  /** Parses an ident from self, viewed as a reader.
  
  Required by
  
  * `get-assignment`
  * `get-model`
  * `get-unsat-assumptions`
  * `get-unsat-core` */
  #[inline(always)]
  fn parse_ident<'a>(
    & self, & 'a [u8]
  ) -> IResult<'a, & 'a [u8], Self::Ident> ;

  /** Parses a value from self, viewed as a reader.

  Required by

  * `get-value`
  * `get-assignment`
  * `get-model` */
  #[inline(always)]
  fn parse_value<'a>(
    & self, & 'a [u8]
  ) -> IResult<'a, & 'a [u8], Self::Value> ;

  /** Parses an expression from self, viewed as a reader.

  Required by

  * `get_assertions` */
  #[inline(always)]
  fn parse_expr<'a>(
    & self, & 'a [u8]
  ) -> IResult<'a, & 'a [u8], Self::Expr> ;

  /** Parses a proof from self, viewed as a reader.

  Required by

  * `get_proof` */
  #[inline(always)]
  fn parse_proof<'a>(
    & self, & 'a [u8]
  ) -> IResult<'a, & 'a [u8], Self::Proof> ;
}

impl ParseSmt2 for () {
  type Ident = () ;
  type Value = () ;
  type Expr = () ;
  type Proof = () ;
  fn parse_ident<'a>(
    & self, _: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], Self::Ident> {
    panic!("parser on () called")
  }
  fn parse_value<'a>(
    & self, _: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], Self::Value> {
    panic!("parser on () called")
  }
  fn parse_expr<'a>(
    & self, _: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], Self::Expr> {
    panic!("parser on () called")
  }
  fn parse_proof<'a>(
    & self, _: & 'a [u8]
  ) -> IResult<'a, & 'a [u8], Self::Proof> {
    panic!("parser on () called")
  }
}



/** SMT Lib 2 logics. */
#[allow(non_camel_case_types)]
pub enum Logic {
  /** Quantifier-free uninterpreted functions. */
  QF_UF,
  /** Quantifier-free linear integer arithmetic. */
  QF_LIA,
  /** Quantifier-free non-linear integer arithmetic. */
  QF_NIA,
  /** Quantifier-free linear real arithmetic. */
  QF_LRA,
  /** Quantifier-free arrays, uninterpreted functions, linear integer
  arithmetic. */
  QF_AUFLIA,
  /** Quantifier-free arrays, uninterpreted functions, linear integer
  arithmetic. */
  AUFLIA,
  /** Arrays, uninterpreted functions, linear integer/real arithmetic. */
  AUFLIRA,
  /** arrays, uninterpreted functions, non-linear integer/real arithmetic. */
  AUFNIRA,
  /** Linear real arithmetic. */
  LRA,
}

impl Logic {
  /** Prints the logic in a writer in SMT Lib 2 format. */
  pub fn to_smt2(& self, writer: & mut io::Write, _: ()) -> IoResUnit {
    use self::Logic::* ;
    match * self {
      QF_UF => write!(writer, "QF_UF"),
      QF_LIA => write!(writer, "QF_LIA"),
      QF_NIA => write!(writer, "QF_NIA"),
      QF_LRA => write!(writer, "QF_LRA"),
      QF_AUFLIA => write!(writer, "QF_AUFLIA"),
      AUFLIA => write!(writer, "AUFLIA"),
      AUFLIRA => write!(writer, "AUFLIRA"),
      AUFNIRA => write!(writer, "AUFNIRA"),
      LRA => write!(writer, "LRA"),
    }
  }
}