/*!
Basic types used by the library.
*/

use std::io ;

use nom::IResult ;


/** Alias for `io` results of unit. */
pub type IoResUnit = io::Result<()> ;
/** Alias for `io` results of `bool`. */
pub type IoResBool = io::Result<bool> ;
/** Alias for generic `io` results. */
pub type IoRes<T> = io::Result<T> ;



/** Unexpected result for an SMT lib 2 command. */
pub enum UnexSmtResult {
  /** An unsupported command was issue. */
  Unsupported,
  /** A command produced an error. */
  Error(String)
}



/** Can be printed to the SMT lib 2 standard. Parametrized by some type for
printing info, typically the unrolling depth in model-checking. */
pub trait PrintSmt2<T> {
  /** Prints something in the SMT lib 2 standard. */
  fn to_smt2(& self, writer: & mut io::Write, info: T) -> IoResUnit ;
}



/** SMT lib 2 logics. */
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

impl PrintSmt2<()> for Logic {
  fn to_smt2(& self, writer: & mut io::Write, _: ()) -> IoResUnit {
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



/** Generic type for the parsing of an SMT lib 2 command. */
pub type SmtParseResult<T> = Result<T, UnexSmtResult> ;



/** Parse methods. Not all of them are necessary depending on the queries wanted. See each method for details.*/
pub trait ParseSmt2<Ident, Value, Expr, Proof> : io::Read {
  /** Parses an ident from self, viewed as a reader.
  
  Required by
  
  * `get-assignment`
  * `get-model`
  * `get-unsat-assumptions`
  * `get-unsat-core` */
  fn parse_ident<'a, F>(& self) -> F
  where F: Fn(&'a [u8]) -> IResult<&'a [u8], Ident> ;

  /** Parses a value from self, viewed as a reader.

  Required by

  * `get-value`
  * `get-assignment`
  * `get-model` */
  fn parse_value<'a, F>(& self) -> F
  where F: Fn(&'a [u8]) -> IResult<&'a [u8], Value> ;

  /** Parses an expression from self, viewed as a reader.

  Required by

  * `get_assertions` */
  fn parse_expr<'a, F>(& self) -> F
  where F: Fn(&'a [u8]) -> IResult<&'a [u8], Expr> ;

  /** Parses a proof from self, viewed as a reader.

  Required by

  * `get_proof` */
  fn parse_proof<'a, F>(& self) -> F
  where F: Fn(&'a [u8]) -> IResult<&'a [u8], Proof> ;
}