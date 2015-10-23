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
use std::process ;

use nom::IResult ;


/** Alias for `io` results of unit. */
pub type IoResUnit = io::Result<()> ;
/** Alias for `io` results of `bool`. */
pub type IoResBool = io::Result<bool> ;
/** Alias for generic `io` results. */
pub type IoRes<T> = io::Result<T> ;



/** Unexpected result for an SMT lib 2 command. */
#[derive(Debug)]
pub enum UnexSmtRes {
  /** An unsupported command was issue. */
  Unsupported,
  /** A command produced an error. */
  Error(String)
}

/** Result of an SMT query. */
pub type SmtRes<T> = Result<T, UnexSmtRes> ;



/** Can be printed to the SMT lib 2 standard. Parametrized by some type for
printing info, typically the unrolling depth in model-checking. */
pub trait PrintSmt2<T> {
  /** Prints something in the SMT lib 2 standard. */
  fn to_smt2(& self, writer: & mut io::Write, info: T) -> IoResUnit ;
}

impl<'a> PrintSmt2<()> for & 'a str {
  fn to_smt2(& self, writer: & mut io::Write, _: ()) -> IoResUnit {
    write!(writer, "{}", self)
  }
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
pub type SmtParseResult<T> = Result<T, UnexSmtRes> ;



/** Parse methods. Not all of them are necessary depending on the queries wanted. See each method for details.*/
pub trait ParseSmt2 {
  type Ident ;
  type Value ;
  type Expr ;
  type Proof ;

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
  fn parse_ident<'a>(& self, _: & 'a [u8]) -> IResult<'a, & 'a [u8], Self::Ident> {
    panic!("parser on () called")
  }
  fn parse_value<'a>(& self, _: & 'a [u8]) -> IResult<'a, & 'a [u8], Self::Value> {
    panic!("parser on () called")
  }
  fn parse_expr<'a>(& self, _: & 'a [u8]) -> IResult<'a, & 'a [u8], Self::Expr> {
    panic!("parser on () called")
  }
  fn parse_proof<'a>(& self, _: & 'a [u8]) -> IResult<'a, & 'a [u8], Self::Proof> {
    panic!("parser on () called")
  }
}



/** Wrapper a `Child` to implement `Read`. */
pub struct Kid {
  kid: process::Child,
}

impl Kid {

  /** Creates a new Kid. */
  #[inline(always)]
  pub fn mk(kid: process::Child) -> Self { Kid { kid: kid } }

  /** A reference on the underlying child. */
  #[inline(always)]
  pub fn get(& self) -> & process::Child { & self.kid }

  /** Unwraps the underlying child. */
  #[inline(always)]
  pub fn unwrap(self) -> process::Child { self.kid }

  /** Kills the underlying child. */
  pub fn kill(mut self) -> IoResUnit{ self.kid.kill() }

  /** A reference on the child's stdin. */
  #[inline(always)]
  pub fn stdin(& mut self) -> Option<& mut process::ChildStdin> {
    match self.kid.stdin {
      None => None, Some(ref mut stdin) => Some(stdin)
    }
  }

  /** A reference on the child's stderr. */
  #[inline(always)]
  pub fn stderr(& mut self) -> Option<& mut process::ChildStderr> {
    match self.kid.stderr {
      None => None, Some(ref mut stderr) => Some(stderr)
    }
  }

  /** A reference on the child's stdout. */
  #[inline(always)]
  pub fn stdout(& mut self) -> Option<& mut process::ChildStdout> {
    match self.kid.stdout {
      None => None, Some(ref mut stdout) => Some(stdout)
    }
  }

}

impl<'a> io::Read for & 'a mut Kid {
  fn read(& mut self, buf: &mut [u8]) -> io::Result<usize> {
    use ::std::io::{ Read, Error, ErrorKind } ;
    match self.kid.stdout {
      None => Err(
        Error::new(
          ErrorKind::Other, "cannot access reader of child process"
        )
      ),
      Some(ref mut stdout) => {
        let out = stdout.read(buf) ;
        // println!("> read = \"{}\"", ::std::str::from_utf8(buf).unwrap()) ;
        out
      }
    }
  }
}


/** Hack around the `Stepper` from `nom` to handle parsing of a child
process. */
pub mod stepper {
  use nom::{
    StepperState, Producer, IResult, ProducerState
  } ;
  use nom::StepperState::* ;

  /** Stepper designed for child processes. */
  pub struct Stepper<T: Producer> {
    acc: Vec<u8>,
    remaining: Vec<u8>,
    producer: T,
  }

  impl<T: Producer> Stepper<T> {
    /** Creates a new stepper. */
    pub fn new(producer: T) -> Stepper<T> {
      Stepper { acc: Vec::new(), remaining: Vec::new(), producer: producer }
    }

    /** Attempts to parse the output that was previously retrieved. Does **not** read on the producer.*/
    pub fn current_step<'a, F, O>(
      & 'a mut self, parser: F
    ) -> StepperState<'a, O>
    where F: Fn(&'a [u8]) -> IResult<&'a [u8],O> {
      self.acc.clear() ;
      self.acc.extend(self.remaining.iter().cloned()) ;

      match parser(&(self.acc)[..]) {
        IResult::Done(i, o) => {
          self.remaining.clear() ;
          self.remaining.extend(i.iter().cloned()) ;
          StepperState::Value(o)
        },
        IResult::Error(e) => {
          self.remaining.clear() ;
          self.remaining.extend(self.acc.iter().cloned()) ;
          StepperState::ParserError(e)
        },
        IResult::Incomplete(_) =>
          StepperState::Continue,
      }
    }

    /** Reads on the producer and attemps to parse something. */
    pub fn step<'a, F, O>(
      & 'a mut self, parser: F
    ) -> StepperState<'a, O>
    where F: Fn(&'a [u8]) -> IResult<&'a [u8],O> {
      self.acc.clear() ;
      self.acc.extend(self.remaining.iter().cloned()) ;

      /* Incomplete, need more data. */
      let state = self.producer.produce() ;

      match state {
        ProducerState::Data(v) => {
          self.acc.extend(v.iter().cloned())
        },
        ProducerState::Eof(v) => {
          self.acc.extend(v.iter().cloned())
        },
        ProducerState::Continue =>
          return StepperState::Continue,
        ProducerState::ProducerError(u) =>
          return StepperState::ProducerError(u),
      }

      if self.acc.is_empty() { return StepperState::Eof }

      match parser(&(self.acc)[..]) {
        IResult::Done(i, o) => {
          self.remaining.clear() ;
          self.remaining.extend(i.iter().cloned()) ;
          return StepperState::Value(o)
        },
        IResult::Error(e) => {
          self.remaining.clear() ;
          self.remaining.extend(self.acc.iter().cloned()) ;
          return StepperState::ParserError(e)
        },
        IResult::Incomplete(_) => {
          self.remaining.clear() ;
          self.remaining.extend(self.acc.iter().cloned()) ;
          return StepperState::Continue
        },
      }
    }
  }

}