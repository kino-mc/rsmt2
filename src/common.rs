#![ doc = "
Basic types used by the library.
"]

use std::io ;

/// Unexpected result for an SMT lib 2 command.
pub enum UnexSmtResult {
  Unsupported,
  Error(String)
}

/// Generic type for the parsing of an SMT lib 2 command.
pub type SmtParseResult<T> = Result<T, UnexSmtResult> ;

/// Alias for `io` results of unit.
pub type IoResUnit = io::Result<()> ;
/// Alias for `io` results of `bool`.
pub type IoResBool = io::Result<bool> ;
/// Alias for generic `io` results.
pub type IoRes<T> = io::Result<T> ;

/// Can be printed to the SMT lib 2 standard.
pub trait Printable {
  /// Prints something in the SMT lib 2 standard.
  fn to_smt2(& self, writer: & mut io::Write) -> IoResUnit ;
}

/// Can produce a writer.
pub trait Writable {
  /// Returns a writer.
  fn writer(& mut self) -> & mut io::Write ;
}


/// SMT lib 2 logics.
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
  /// Quantifier-free arrays, uninterpreted functions, linear integer
  /// arithmetic.
  QF_AUFLIA,
  /// Quantifier-free arrays, uninterpreted functions, linear integer
  /// arithmetic.
  AUFLIA,
  /// Arrays, uninterpreted functions, linear integer/real arithmetic.
  AUFLIRA,
  /// arrays, uninterpreted functions, non-linear integer/real arithmetic.
  AUFNIRA,
  /// Linear real arithmetic.
  LRA,
}

impl Printable for Logic {
  fn to_smt2(& self, writer: & mut io::Write) -> IoResUnit {
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


/// Parse methods. Not all of them are necessary depending on the queries you
/// will use. See each method for details.
pub trait ParseSmt2<Ident, Value, Expr, Proof> : io::Read {
  /// Parses an ident from self, viewed as a reader.
  ///
  /// ## Required by
  ///
  /// * `get-assignment`
  /// * `get-model`
  /// * `get-unsat-assumptions`
  /// * `get-unsat-core`
  fn parse_ident(& mut self) -> Ident ;

  /// Parses a value from self, viewed as a reader.
  ///
  /// ## Required by
  ///
  /// * `get-value`
  /// * `get-assignment`
  /// * `get-model`
  fn parse_value(& mut self) -> Value ;

  /// Parses an expression from self, viewed as a reader.
  ///
  /// ## Required by
  ///
  /// * `get_assertions`
  fn parse_expr(& mut self) -> Expr ;

  /// Parses a proof from self, viewed as a reader.
  ///
  /// ## Required by
  ///
  /// * `get_proof`
  fn parse_proof(& mut self) -> Proof ;
}