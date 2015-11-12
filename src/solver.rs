// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!
Wrapper around an SMT Lib 2 compliant solver.

The underlying solver runs in a separate process, communication uses system
pipes.
*/


use std::process::{ Command, Stdio } ;
use std::fmt::Debug ;
use std::io ;
use std::io::{ Write, Read } ;
use std::process ;

use nom::multispace ;

use common::* ;
use self::stepper::* ;
use common::UnexSmtRes::* ;
use conf::SolverConf ;
use parse::* ;


macro_rules! try_writer {
  ($e:expr) => (
    match $e {
      Some(writer) => writer,
      None => return Err(
        IOError(
          io::Error::new(
            io::ErrorKind::Other, "cannot access reader of child process"
          )
        )
      ),
    }
  )
}

#[cfg(not(no_parse_success))]
macro_rules! parse_success {
  ($slf:ident for $b:block) => (
    {
      let res = $b ;
      if $slf.conf.get_parse_success() {
        match $slf.parse_success() {
          Ok(()) => res,
          e => e
        }
      } else { res }
    }
  ) ;
}

#[cfg(no_parse_success)]
macro_rules! parse_success {
  ($slf:ident for $b:block) => (
    $b
  ) ;
}

macro_rules! smtry_io {
  ($e:expr) => (
    match $e {
      Ok(something) => something,
      Err(e) => return Err(IOError(e)),
    }
  ) ;
  ($e:expr ; $( $tail:expr );+) => (
    match $e {
      Ok(()) => smtry_io!( $( $tail );+ ),
      Err(e) => return Err(IOError(e)),
    }
  ) ;
}
macro_rules! smt_cast_io {
  ($e:expr) => (
    match $e {
      Ok(something) => Ok(something),
      Err(e) => Err(IOError(e)),
    }
  ) ;
  ($e:expr ; $( $tail:expr );+) => (
    match $e {
      Ok(()) => smt_cast_io!( $( $tail );+ ),
      Err(e) => Err(IOError(e)),
    }
  ) ;
}

macro_rules! stepper_of {
  ($e:expr) => (
    {
      use nom::ReadProducer ;
      let producer = ReadProducer::new(& mut $e, 1000) ;
      Stepper::new(producer)
    }
  ) ;
}

macro_rules! take_step {
  ($stepper:expr, $parser:expr) => (
    match $stepper.current_step($parser) {
      nome::StepperState::Continue => $stepper.step($parser),
      res => res,
    }
  )
}

/** Contains an actual solver process. */
pub struct Solver<
  Parser: ParseSmt2
> {
  /** The command used to run the solver. */
  cmd: Command,
  /** The actual solver child process. */
  kid: Kid,
  /** The solver specific information. */
  conf: SolverConf,
  /** The parser. */
  parser: Parser,
}

impl<
  /* Parsing-related type parameters. */
  Parser: ParseSmt2
> Solver<Parser> {

  /** Creates a new solver. */
  pub fn mk(
    cmd: Command, conf: SolverConf, parser: Parser
  ) -> SmtRes<Self> {
    let mut cmd = cmd ;
    /* Adding configuration options to the command. */
    cmd.args(conf.get_options()) ;
    /* Setting up pipes for child process. */
    cmd.stdin(Stdio::piped()) ;
    cmd.stdout(Stdio::piped()) ;
    cmd.stderr(Stdio::piped()) ;
    /* Spawning child process. */
    match cmd.spawn() {
      Ok(kid) => {
        /* Successful, creating solver. */
        let mut solver = Solver {
          cmd: cmd, kid: Kid::mk(kid), conf: conf, parser: parser
        } ;
        /* Activate parse success if asked. */
        if solver.conf.get_parse_success() {
          match solver.print_success() {
            Ok(()) => (),
            Err(e) => {
              solver.kill().unwrap() ;
              return Err(e)
            }
          }
        } ;
        /* Activating interactive mode. */
        try!( solver.interactive_mode() ) ;
        /* Done. */
        Ok(solver)
      },
      Err(e) => Err(IOError(e)),
    }
  }

  /** Kills the underlying solver. */
  #[inline(always)]
  pub fn kill(self) -> IoRes<(Command, SolverConf)> {
    let (cmd,conf,kid) = (self.cmd, self.conf, self.kid) ;
    match kid.kill() {
      Ok(()) => Ok((cmd, conf)),
      Err(e) => Err(e)
    }
  }

  /** Returns a pointer to the writer on the stdin of the process. */
  #[inline(always)]
  fn writer(& mut self) -> Option<& mut process::ChildStdin> {
    self.kid.stdin()
  }

  // /** Returns a pointer to the reader on the stdout of the process. */
  // #[inline(always)]
  // fn out_reader(& mut self) -> Option<& mut process::ChildStdout> {
  //   self.kid.stdout()
  // }

  // /** Gets the standard error output of the process as a string. */
  // #[inline]
  // fn out_as_string(& mut self) -> IoRes<String> {
  //   let mut s = String::new() ;
  //   match self.out_reader() {
  //     Some(stdout) => match stdout.read_to_string(& mut s) {
  //       Ok(_) => Ok(s),
  //       Err(e) => Err(e),
  //     },
  //     None => Err(
  //       io::Error::new(
  //         io::ErrorKind::Other, "cannot access stdout of child process"
  //       )
  //     ),
  //   }
  // }

  /** Returns a pointer to the reader on the stderr of the process. */
  #[inline(always)]
  fn err_reader(& mut self) -> Option<& mut process::ChildStderr> {
    self.kid.stderr()
  }

  /** Gets the standard error output of the process as a string. */
  #[inline]
  pub fn err_as_string(& mut self) -> io::Result<String> {
    let mut s = String::new() ;
    match self.err_reader() {
      Some(stdout) => match stdout.read_to_string(& mut s) {
        Ok(_) => Ok(s),
        Err(e) => Err(e),
      },
      None => Err(
        io::Error::new(
          io::ErrorKind::Other, "cannot access stderr of child process"
        )
      ),
    }
  }


  // Comment things.

  /** Prints some lines as SMT lib 2 comments. */
  #[inline]
  pub fn comments(
    & mut self, lines: ::std::str::Lines
  ) -> UnitSmtRes {
    let mut writer = try_writer!( self.writer() ) ;
    for line in lines {
      smtry_io!( write!(writer, ";; {}\n", line) )
    } ;
    smt_cast_io!( write!(writer, "\n") )
  }
  /** Prints some text as comments. Input is sanitized in case it contains
  newlines. */
  #[inline(always)]
  pub fn comment(& mut self, txt: & str) -> UnitSmtRes {
    self.comments(txt.lines())
  }


  // |===| (Re)starting and terminating.

  /** Resets the underlying solver. Restarts the kid process if no reset
  command is supported. */
  #[inline(always)]
  pub fn reset(
    & mut self
  ) -> UnitSmtRes {
    let mut writer = try_writer!( self.writer() ) ;
    smt_cast_io!( write!(writer, "(reset)\n") )
  }
  #[inline]
  /** Sets the logic. */
  pub fn set_logic(
    & mut self, logic: & Logic
  ) -> UnitSmtRes {
    parse_success!(
      self for {
        let mut writer = try_writer!( self.writer() ) ;
        smt_cast_io!(
          write!(writer, "(set-logic ") ;
          logic.to_smt2(writer, ()) ;
          write!(writer, ")\n")
        )
      }
    )
  }
  /** Set option command. */
  #[inline]
  pub fn set_option<Value: ::std::fmt::Display>(
    & mut self, option: & str, value: Value
  ) -> UnitSmtRes {
    match option {
      ":interactive_mode" => return Err(
        Error(
          "illegal set-option on interactive mode".to_string()
        )
      ),
      ":print_success" => return Err(
        Error(
          "illegal set-option on print success, \
          use `SmtConf` to activate it".to_string()
        )
      ),
      _ => (),
    } ;
    parse_success!(
      self for {
        let mut writer = try_writer!( self.writer() ) ;
        smt_cast_io!( write!(writer, "(set-option {} {})\n", option, value) )
      }
    )
  }
  /** Activates interactive mode. */
  #[inline(always)]
  fn interactive_mode(& mut self) -> UnitSmtRes {
    parse_success!(
      self for {
        let mut writer = try_writer!( self.writer() ) ;
        smt_cast_io!(
          write!(writer, "(set-option :interactive-mode true)\n")
        )
      }
    )
  }
  /** Activates print success. */
  #[inline(always)]
  fn print_success(& mut self) -> UnitSmtRes {
    parse_success!(
      self for {
        let mut writer = try_writer!( self.writer() ) ;
        smt_cast_io!(
          write!(writer, "(set-option :print-success true)\n")
        )
      }
    )
  }
  /** Activates unsat core production. */
  #[inline(always)]
  pub fn produce_unsat_core(& mut self) -> UnitSmtRes {
    parse_success!(
      self for {
        let mut writer = try_writer!( self.writer() ) ;
        smt_cast_io!(
          write!(writer, "(set-option :produce-unsat-cores true)\n")
        )
      }
    )
  }
  /** Shuts the solver down. */
  #[inline(always)]
  pub fn exit(& mut self) -> UnitSmtRes {
    parse_success!(
      self for {
        let mut writer = try_writer!( self.writer() ) ;
        smt_cast_io!(
          write!(writer, "(exit)\n")
        )
      }
    )
  }


  // |===| Modifying the assertion stack.

  /** Pushes `n` layers on the assertion stack. */
  #[inline(always)]
  pub fn push(& mut self, n: & u8) -> UnitSmtRes {
    parse_success!(
      self for {
        let mut writer = try_writer!( self.writer() ) ;
        smt_cast_io!(
          write!(writer, "(push {})\n", n)
        )
      }
    )
  }
  /** Pops `n` layers off the assertion stack. */
  #[inline(always)]
  pub fn pop(& mut self, n: & u8) -> UnitSmtRes {
    parse_success!(
      self for {
        let mut writer = try_writer!( self.writer() ) ;
        smt_cast_io!(
          write!(writer, "(pop {})\n", n)
        )
      }
    )
  }
  /** Resets the assertions in the solver. */
  #[inline(always)]
  pub fn reset_assertions(& mut self) -> UnitSmtRes {
    parse_success!(
      self for {
        let mut writer = try_writer!( self.writer() ) ;
        smt_cast_io!(
          write!(writer, "(reset-assertions)\n")
        )
      }
    )
  }


  // |===| Introducing new symbols.

  /** Declares a new sort. */
  #[inline]
  pub fn declare_sort<Sort: Sort2Smt>(
    & mut self, sort: & Sort, arity: & u8
  ) -> UnitSmtRes {
    parse_success!(
      self for {
        let mut writer = try_writer!( self.writer() ) ;
        smt_cast_io!(
          write!(writer, "(declare-sort ") ;
          sort.sort_to_smt2(writer) ;
          write!(writer, " {})\n", arity)
        )
      }
    )
  }
  /** Defines a new sort. */
  #[inline]
  pub fn define_sort<
    Sort: Sort2Smt, I, Expr1: Expr2Smt<I>, Expr2: Expr2Smt<I>
  >(
    & mut self, sort: & Sort, args: & [ Expr1 ], body: & Expr2, info: & I
  ) -> UnitSmtRes {
    parse_success!(
      self for {
        let mut writer = try_writer!( self.writer() ) ;
        smtry_io!(
          write!(writer, "( define-sort ") ;
          sort.sort_to_smt2(writer) ;
          write!(writer, "\n   ( ")
        ) ;
        for arg in args {
          smtry_io!(
            arg.expr_to_smt2(writer, info) ;
            write!(writer, " ")
          ) ;
        } ;
        smt_cast_io!(
          write!(writer, ")\n   ") ;
          body.expr_to_smt2(writer, info) ;
          write!(writer, "\n)\n")
        )
      }
    )
  }
  /** Declares a new function symbol. */
  #[inline]
  pub fn declare_fun<Sort: Sort2Smt, I, Sym: Sym2Smt<I>> (
    & mut self, symbol: & Sym, args: & [ Sort ], out: & Sort, info: & I
  ) -> UnitSmtRes {
    parse_success!(
      self for {
        let mut writer = try_writer!( self.writer() ) ;
        smtry_io!(
          write!(writer, "(declare-fun ") ;
          symbol.sym_to_smt2(writer, info) ;
          write!(writer, " ( ")
        ) ;
        for arg in args {
          smtry_io!(
            arg.sort_to_smt2(writer) ;
            write!(writer, " ")
          ) ;
        } ;
        smt_cast_io!(
          write!(writer, ") ") ;
          out.sort_to_smt2(writer) ;
          write!(writer, ")\n")
        )
      }
    )
  }
  /** Declares a new constant. */
  #[inline]
  pub fn declare_const<Sort: Sort2Smt, I, Sym: Sym2Smt<I>> (
    & mut self, symbol: & Sym, out_sort: & Sort, info: & I
  ) -> UnitSmtRes {
    parse_success!(
      self for {
        let mut writer = try_writer!( self.writer() ) ;
        smt_cast_io!(
          write!(writer, "(declare-const ") ;
          symbol.sym_to_smt2(writer, info) ;
          write!(writer, " ") ;
          out_sort.sort_to_smt2(writer) ;
          write!(writer, ")\n")
        )
      }
    )
  }
  /** Defines a new function symbol. */
  #[inline]
  pub fn define_fun<
    I, Sort: Sort2Smt, Sym1: Sym2Smt<I>, Sym2: Sym2Smt<I>, Expr: Expr2Smt<I>
  >(
    & mut self, symbol: & Sym1, args: & [ (Sym2, Sort) ],
    out: & Sort, body: & Expr, info: & I
  ) -> UnitSmtRes {
    parse_success!(
      self for {
        let mut writer = try_writer!( self.writer() ) ;
        smtry_io!(
          write!(writer, "(define-fun ") ;
          symbol.sym_to_smt2(writer, info) ;
          write!(writer, " ( ")
        ) ;
        for arg in args {
          let (ref sym, ref sort) = * arg ;
          smtry_io!(
            write!(writer, "(") ;
            sym.sym_to_smt2(writer, info) ;
            write!(writer, " ") ;
            sort.sort_to_smt2(writer) ;
            write!(writer, ") ")
          )
        } ;
        smt_cast_io!(
          write!(writer, ") ") ;
          out.sort_to_smt2(writer) ;
          write!(writer, "\n   ") ;
          body.expr_to_smt2(writer, info) ;
          write!(writer, "\n)\n")
        )
      }
    )
  }
  /** Defines some new (possibily mutually) recursive functions. */
  #[inline]
  pub fn define_funs_rec<
    I, Sort: Sort2Smt, Sym: Sym2Smt<I>, Expr: Expr2Smt<I>
  >(
    & mut self, funs: & [ (Sym, & [ (Sym, Sort) ], Sort, Expr) ], info: & I
  ) -> UnitSmtRes {
    parse_success!(
      self for {
        let mut writer = try_writer!( self.writer() ) ;
        // Header.
        smtry_io!( write!(writer, "(define-funs-rec (\n") ) ;

        // Signatures.
        for fun in funs {
          let (ref sym, ref args, ref out, _) = * fun ;
          smtry_io!(
            write!(writer, "   (");
            sym.sym_to_smt2(writer, info) ;
            write!(writer, " ( ")
          ) ;
          for arg in * args {
            let (ref sym, ref sort) = * arg ;
            smtry_io!(
              write!(writer, "(") ;
              sym.sym_to_smt2(writer, info) ;
              write!(writer, " ") ;
              sort.sort_to_smt2(writer) ;
              write!(writer, ") ")
            )
          } ;
          smtry_io!(
            write!(writer, ") ") ;
            out.sort_to_smt2(writer) ;
            write!(writer, ")\n")
          )
        } ;
        smtry_io!( write!(writer, " ) (") ) ;

        // Bodies
        for fun in funs {
          let (_, _, _, ref body) = * fun ;
          smtry_io!(
            write!(writer, "\n   ") ;
            body.expr_to_smt2(writer, info)
          )
        } ;
        smt_cast_io!( write!(writer, "\n )\n)\n") )
      }
    )
  }
  /** Defines a new recursive function. */
  #[inline]
  pub fn define_fun_rec<
    I, Sort: Sort2Smt, Sym: Sym2Smt<I>, Expr: Expr2Smt<I>
  >(
    & mut self,  symbol: & Sym, args: & [ (Sym, Sort) ],
    out: & Sort, body: & Expr, info: & I
  ) -> UnitSmtRes {
    parse_success!(
      self for {
        let mut writer = try_writer!( self.writer() ) ;
        // Header.
        smtry_io!( write!(writer, "(define-fun-rec (\n") ) ;

        // Signature.
        smtry_io!(
          write!(writer, "   (") ;
          symbol.sym_to_smt2(writer, info) ;
          write!(writer, " ( ")
        ) ;
        for arg in args {
          let (ref sym, ref sort) = * arg ;
          smtry_io!(
            write!(writer, "(") ;
            sym.sym_to_smt2(writer, info) ;
            write!(writer, " ") ;
            sort.sort_to_smt2(writer) ;
            write!(writer, ") ")
          )
        } ;
        smtry_io!(
          write!(writer, ") ") ;
          out.sort_to_smt2(writer) ;
          write!(writer, ")\n") ;
          write!(writer, " ) (")
        ) ;

        // Body.
        smt_cast_io!(
          write!(writer, "\n   ") ;
          body.expr_to_smt2(writer, info) ;
          write!(writer, "\n )\n)\n")
        )
      }
    )
  }


  // |===| Asserting and inspecting formulas.

  /** Asserts an expression with some print information. */
  #[inline]
  pub fn assert<I, Expr: Expr2Smt<I>>(
    & mut self, expr: & Expr, info: & I
  ) -> UnitSmtRes {
    parse_success!(
      self for {
        let mut writer = try_writer!( self.writer() ) ;
        smt_cast_io!(
          write!(writer, "(assert\n  ") ;
          expr.expr_to_smt2(writer, info) ;
          write!(writer, "\n)\n")
        )
      }
    )
  }

  // |===| Inspecting settings.

  /** Get info command. */
  #[inline(always)]
  pub fn get_info(& mut self, flag: & str) -> UnitSmtRes {
    let mut writer = try_writer!( self.writer() ) ;
    smt_cast_io!( write!(writer, "(get-info {})\n", flag) )
  }
  /** Get option command. */
  #[inline(always)]
  pub fn get_option(& mut self, option: & str) -> UnitSmtRes {
    let mut writer = try_writer!( self.writer() ) ;
    smt_cast_io!( write!(writer, "(get-option {})\n", option) )
  }

  // |===| Script information.

  /** Set info command. */
  #[inline(always)]
  pub fn set_info(& mut self, attribute: & str) -> UnitSmtRes {
    let mut writer = try_writer!( self.writer() ) ;
    smt_cast_io!( write!(writer, "(set-info {})\n", attribute) )
  }
  /** Echo command. */
  #[inline(always)]
  pub fn echo(& mut self, text: & str) -> UnitSmtRes {
    let mut writer = try_writer!( self.writer() ) ;
    smt_cast_io!( write!(writer, "(echo \"{}\")\n", text) )
  }


  // |===| Parsing simple stuff.

  /** Parse success. */
  #[inline]
  fn parse_success(& mut self) -> SuccessRes {
    use nom::StepperState::* ;
    let mut stepper = stepper_of!(self.kid) ;
    loop {
      match stepper.step( success ) {
        Value( e ) => return e,
        Continue => continue,
        ParserError(::nom::Err::Position(p,txt)) => {
          panic!("at {}: \"{}\"", p, ::std::str::from_utf8(txt).unwrap())
        },
        step => { panic!("step = {:?}", step) },
      }
    }
  }
}


impl<Parser: ParseSmt2> async::Asynced<
  Parser::I, Parser::Ident, Parser::Value, Parser::Expr, Parser::Proof
> for Solver<Parser> {

  /** Check-sat command. */
  #[inline]
  fn check_sat(& mut self) -> UnitSmtRes {
    let mut writer = try_writer!( self.writer() ) ;
    smt_cast_io!( write!(writer, "(check-sat)\n") )
  }

  /** Parse the result of a check-sat. */
  #[inline]
  fn parse_sat(& mut self) -> SmtRes<bool> {
    use nom::StepperState::* ;
    let mut stepper = stepper_of!(self.kid) ;
    loop {
      match stepper.step( check_sat ) {
        Value( res ) => return res,
        Continue => { println!("continue") },
        ParserError(::nom::Err::Position(p,txt)) => {
          panic!("at {}: \"{}\"", p, ::std::str::from_utf8(txt).unwrap())
        },
        step => panic!("{:?}", step),
      }
    }
  }

  /** Get model command. */
  #[inline(always)]
  fn get_model(& mut self) -> UnitSmtRes {
    let mut writer = try_writer!( self.writer() ) ;
    smt_cast_io!( write!(writer, "(get-model)\n") )
  }

  /** Parses the result of a get-model. */
  #[inline]
  fn parse_model(& mut self) -> SmtRes<Vec<(
    Parser::Ident, Parser::Value
  )>> where Parser::Value: Debug, Parser::Ident: Debug {
    use nom::StepperState::* ;
    use parse::{ open_paren, close_paren, unexpected } ;
    let parser = & self.parser ;
    let mut stepper = stepper_of!(self.kid) ;

    loop {
      match stepper.step (
        closure!(
          alt!(
            map!( unexpected, |e| Err(e) ) |
            chain!(
              open_paren ~
              opt!(multispace) ~
              tag!("model") ~
              vec: many0!(
                chain!(
                  open_paren ~
                  opt!(multispace) ~
                  tag!("define-fun") ~
                  multispace ~
                  id: call!(|bytes| parser.parse_ident(bytes)) ~
                  open_paren ~
                  close_paren ~
                  opt!(multispace) ~
                  alt!( tag!("bool") | tag!("int") | tag!("real") ) ~
                  opt!(multispace) ~
                  val: call!(|bytes| parser.parse_value(bytes)) ~
                  close_paren,
                  || (id, val)
                )
              ) ~
              close_paren,
              || Ok(vec)
            )
          )
        )
      ) {
        Value( Ok(vec) ) => return Ok(vec),
        Value( Err(unex) ) => return Err(unex),
        ParserError(::nom::Err::Position(p,txt)) => return Err(
          Error(
            format!(
              "parser error at {}: \"{}\"",
              p, ::std::str::from_utf8(txt).unwrap()
            )
          )
        ),
        ParserError(e) => return Err(
          Error( format!("parser error: \"{:?}\"", e) )
        ),
        ProducerError(i) => return Err(
          Error( format!("producer error ({})",i ) )
        ),
        _ => continue,
      }
    }
  }


  /** Parser the result of a get-values. */
  #[inline]
  fn parse_values(& mut self, info: & Parser::I) -> SmtRes<
    Vec<(Parser::Expr, Parser::Value)>
  > {
    use nom::StepperState::* ;
    use parse::{ open_paren, close_paren, unexpected } ;
    let parser = & self.parser ;
    let mut stepper = stepper_of!(self.kid) ;

    loop {
      match stepper.step (
        closure!(
          alt!(
            map!( unexpected, |e| Err(e) ) |
            chain!(
              open_paren ~
              vec: many0!(
                chain!(
                  open_paren ~
                  opt!(multispace) ~
                  expr: call!(|bytes| parser.parse_expr(bytes, info)) ~
                  multispace ~
                  val: call!(|bytes| parser.parse_value(bytes)) ~
                  close_paren,
                  || (expr, val)
                )
              ) ~
              close_paren,
              || Ok(vec)
            )
          )
        )
      ) {
        Value( Ok(vec) ) => return Ok(vec),
        Value( Err(unex) ) => return Err(unex),
        ParserError(::nom::Err::Position(p,txt)) => return Err(
          Error(
            format!(
              "parser error at {}: \"{}\"",
              p, ::std::str::from_utf8(txt).unwrap()
            )
          )
        ),
        ParserError(e) => return Err(
          Error( format!("parser error: \"{:?}\"", e) )
        ),
        ProducerError(i) => return Err(
          Error( format!("producer error ({})",i ) )
        ),
        _ => continue,
      }
    }
  }

  /** Get assertions command. */
  #[inline]
  fn get_assertions(& mut self) -> UnitSmtRes {
    let mut writer = try_writer!( self.writer() ) ;
    smt_cast_io!( write!(writer, "(get-assertions)\n") )
  }
  /** Get assignment command. */
  #[inline(always)]
  fn get_assignment(& mut self) -> UnitSmtRes {
    let mut writer = try_writer!( self.writer() ) ;
    smt_cast_io!( write!(writer, "(get-assignment)\n") )
  }
  /** Get unsat assumptions command. */
  #[inline(always)]
  fn get_unsat_assumptions(& mut self) -> UnitSmtRes {
    let mut writer = try_writer!( self.writer() ) ;
    smt_cast_io!( write!(writer, "(get-unsat-assumptions)\n") )
  }
  /** Get proof command. */
  #[inline(always)]
  fn get_proof(& mut self) -> UnitSmtRes {
    let mut writer = try_writer!( self.writer() ) ;
    smt_cast_io!( write!(writer, "(get-proof)\n") )
  }
  /** Get unsat core command. */
  #[inline(always)]
  fn get_unsat_core(& mut self) -> UnitSmtRes {
    let mut writer = try_writer!( self.writer() ) ;
    smt_cast_io!( write!(writer, "(get-unsat-core)\n") )
  }
}


impl<I, Parser: ParseSmt2, Ident: Sym2Smt<I>> async::AsyncedIdentPrint<
  I,
  Parser::I, Parser::Ident, Parser::Value, Parser::Expr, Parser::Proof,
  Ident
> for Solver<Parser> {

  /** Check-sat assuming command. */
  #[inline]
  fn check_sat_assuming(
    & mut self, bool_vars: & [ Ident ], info: & I
  ) -> UnitSmtRes {
    match self.conf.get_check_sat_assuming() {
      & Ok(cmd) => {
        let mut writer = try_writer!( self.writer() ) ;
        smtry_io!( write!(writer, "({}\n ", cmd) );
        for sym in bool_vars {
          smtry_io!(
            write!(writer, " ") ;
            sym.sym_to_smt2(writer, info)
          )
        } ;
        smt_cast_io!( write!(writer, "\n)\n") )
      },
      _ => panic!("check-sat-assuming command is not supported")
    }
  }
}


impl<Parser: ParseSmt2, Expr: Expr2Smt<Parser::I>> async::AsyncedExprPrint<
  Parser::I,
  Parser::I, Parser::Ident, Parser::Value, Parser::Expr, Parser::Proof,
  Expr
> for Solver<Parser> {

  /** Get value command. */
  #[inline]
  fn get_values(
    & mut self, exprs: & [ Expr ], info: & Parser::I
  ) -> UnitSmtRes {
    let mut writer = try_writer!( self.writer() ) ;
    smtry_io!( write!(writer, "(get-value (") ) ;
    for e in exprs {
      smtry_io!(
        write!(writer, "\n  ") ;
        e.expr_to_smt2(writer, info)
      )
    } ;
    smt_cast_io!( write!(writer, "\n) )\n") )
  }
}


impl<Parser: ParseSmt2> sync::Synced<
  Parser::I, Parser::Ident, Parser::Value, Parser::Expr, Parser::Proof
> for Solver<Parser> {}

impl<I, Parser: ParseSmt2, Ident: Sym2Smt<I>> sync::SyncedIdentPrint<
  I,
  Parser::I, Parser::Ident, Parser::Value, Parser::Expr, Parser::Proof,
  Ident
> for Solver<Parser> {}

impl<Parser: ParseSmt2, Expr: Expr2Smt<Parser::I>> sync::SyncedExprPrint<
  Parser::I, Parser::Ident, Parser::Value, Parser::Expr, Parser::Proof, Expr
> for Solver<Parser> {}





// /** Can parse the result of SMT lib 2 queries. */
// impl<
//   Ident, Value, Expr, Proof
// > Smt2Parse<Ident, Value, Expr, Proof> for Solver {

//   fn parse_assertions(& mut self) -> IoRes<Option<Vec<Expr>>> {
//     Ok(None)
//   }

//   fn parse_value(& mut self) -> IoRes<Option<Vec<Value>>> {
//     Ok(None)
//   }
//   fn parse_assignment(& mut self) -> IoRes<Option<Vec<(Ident, Value)>>> {
//     Ok(None)
//   }
//   fn parse_model(& mut self) -> IoRes<Option<Vec<(Ident, Value)>>> {
//     Ok(None)
//   }

//   fn parse_unsat_assumptions(& mut self) -> IoRes<Option<Vec<Ident>>> {
//     Ok(None)
//   }
//   fn parse_proof(& mut self) -> IoRes<Option<Proof>> {
//     Ok(None)
//   }
//   fn parse_unsat_core(& mut self) -> IoRes<Option<Vec<Ident>>> {
//     Ok(None)
//   }

//   fn parse_info(& mut self) -> IoRes<Option<String>> {
//     Ok(None)
//   }
//   fn parse_option(& mut self) -> IoRes<Option<String>> {
//     Ok(None)
//   }

// }

// impl<
//   Ident: Printable,
//   Value,
//   Sort: Printable,
//   Expr: Printable,
//   Proof,
// > Smt2GetNow<Ident, Value, Sort, Expr, Proof> for Solver {}

// impl<
//   Ident: Printable,
//   Value,
//   Sort: Printable,
//   Expr: Printable,
//   Proof,
// > Smt2Solver<Ident, Value, Sort, Expr, Proof> for Solver {}



/** Asynchronous solver queries.

Queries are printed on the solver's standard input but the result is not
parsed. It must be retrieved separately. */
pub mod async {
  use common::* ;

  /** Asynchronous queries with no printing. */
  pub trait Asynced<PInfo, PIdent, PValue, PExpr, PProof> {
    /** Check-sat command. */
    fn check_sat(& mut self) -> UnitSmtRes ;
    /** Parse the result of a check-sat. */
    fn parse_sat(& mut self) -> SmtRes<bool> ;

    /** Get-model command. */
    fn get_model(& mut self) -> UnitSmtRes ;
    /** Parse the result of a get-model. */
    fn parse_model(& mut self) -> SmtRes<Vec<(PIdent, PValue)>> ;
    /** Parse the result of a get-values. */
    fn parse_values(& mut self, & PInfo) -> SmtRes<Vec<(PExpr, PValue)>> ;

    /** Get-assertions command. */
    fn get_assertions(& mut self) -> UnitSmtRes ;
    /** Get-assignment command. */
    fn get_assignment(& mut self) -> UnitSmtRes ;
    /** Get-unsat-assumptions command. */
    fn get_unsat_assumptions(& mut self) -> UnitSmtRes ;
    /** Get-proop command. */
    fn get_proof(& mut self) -> UnitSmtRes ;
    /** Get-unsat-core command. */
    fn get_unsat_core(& mut self) -> UnitSmtRes ;
  }

  /** Asynchronous queries with ident printing. */
  pub trait AsyncedIdentPrint<
    I, PInfo, PIdent, PValue, PExpr, PProof, Ident: Sym2Smt<I>
  > : Asynced<PInfo, PIdent, PValue, PExpr, PProof> {
    /** Check-sat with assumptions command. */
    fn check_sat_assuming(& mut self, & [ Ident ], & I) -> UnitSmtRes ;
  }

  /** Asynchronous queries with expr printing. */
  pub trait AsyncedExprPrint<
    I, PInfo, PIdent, PValue, PExpr, PProof, Expr: Expr2Smt<I>
  > : Asynced<PInfo, PIdent, PValue, PExpr, PProof> {
    /** Get-values command. */
    fn get_values(& mut self, & [ Expr ], & I) -> UnitSmtRes ;
  }

  macro_rules! try_cast {
    ($e:expr) => (
      match $e {
        Ok(something) => something,
        Err(e) => return Err(e),
      }
    ) ;
  }
}

/** Synchronous solver queries.

Queries are issued to the solver and the result is immediately printed. */
pub mod sync {
  use common::* ;
  use super::async::* ;

  macro_rules! try_cast {
    ($e:expr) => (
      match $e {
        Ok(something) => something,
        Err(e) => return Err(e),
      }
    ) ;
  }

  /** Synchrous queries with no printing. */
  pub trait Synced<
    I, PIdent, PValue, PExpr, PProof
  > : Sized + Asynced<I, PIdent, PValue, PExpr, PProof> {

    /** Check-sat command. */
    fn check_sat(& mut self) -> SmtRes<bool> {
      try_cast!(
        (self as & mut Asynced<
          I, PIdent, PValue, PExpr, PProof
        >).check_sat()
      ) ;
      self.parse_sat()
    }

    /** Get-model command. */
    fn get_model(& mut self) -> SmtRes<Vec<(PIdent, PValue)>> {
      try_cast!(
        (self as & mut Asynced<
          I, PIdent, PValue, PExpr, PProof
        >).get_model()
      ) ;
      self.parse_model()
    }
    
  }

  /** Synchrous queries with ident printing. */
  pub trait SyncedIdentPrint<
    I, PInfo, PIdent, PValue, PExpr, PProof, Ident: Sym2Smt<I>
  > : Sized + AsyncedIdentPrint<
    I, PInfo, PIdent, PValue, PExpr, PProof, Ident
  > {

    /** Check-sat assuming command. */
    fn check_sat_assuming(
      & mut self, idents: & [ Ident ], info: & I
    ) -> SmtRes<bool> {
      try_cast!(
        (self as & mut AsyncedIdentPrint<
          I, PInfo, PIdent, PValue, PExpr, PProof, Ident
        >).check_sat_assuming(idents, info)
      ) ;
      self.parse_sat()
    }
    
  }

  /** Synchrous queries with expr printing. */
  pub trait SyncedExprPrint<
    I, PIdent, PValue, PExpr, PProof, Expr: Expr2Smt<I>
  > : Sized + AsyncedExprPrint<I, I, PIdent, PValue, PExpr, PProof, Expr> {

    /** Get-values command. */
    fn get_values(
      & mut self, exprs: & [ Expr ], info: & I
    ) -> SmtRes<Vec<(PExpr, PValue)>> {
      try_cast!(
        (self as & mut AsyncedExprPrint<
          I, I, PIdent, PValue, PExpr, PProof, Expr
        >).get_values(exprs, info)
      ) ;
      self.parse_values(info)
    }
  }

}







/** Wraps a `Child` to implement `Read`. */
struct Kid {
  kid: process::Child,
}

impl Kid {

  /** Creates a new Kid. */
  #[inline(always)]
  pub fn mk(kid: process::Child) -> Self { Kid { kid: kid } }

  // /** A reference on the underlying child. */
  // #[inline(always)]
  // pub fn get(& self) -> & process::Child { & self.kid }

  // /** Unwraps the underlying child. */
  // #[inline(always)]
  // pub fn unwrap(self) -> process::Child { self.kid }

  /** Kills the underlying child. */
  pub fn kill(mut self) -> IoResUnit { self.kid.kill() }

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

  // /** A reference on the child's stdout. */
  // #[inline(always)]
  // pub fn stdout(& mut self) -> Option<& mut process::ChildStdout> {
  //   match self.kid.stdout {
  //     None => None, Some(ref mut stdout) => Some(stdout)
  //   }
  // }

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
mod stepper {
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