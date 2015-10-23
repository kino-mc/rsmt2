// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!
Implements all the printing and parsing methods for the SMT lib 2 standard.
*/


use std::process::{ Command, Stdio } ;
use std::fmt::Debug ;
use std::io ;
use std::io::{ Write, Read } ;
use std::process ;

use nom::multispace ;

use common::* ;
use common::stepper::* ;
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

/** Contains the actual solver process. */
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
  pub fn kill(self) -> io::Result<(Command, SolverConf)> {
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

  /** Returns a pointer to the reader on the stdout of the process. */
  #[inline(always)]
  fn out_reader(& mut self) -> Option<& mut process::ChildStdout> {
    self.kid.stdout()
  }

  /** Returns a pointer to the reader on the stderr of the process. */
  #[inline(always)]
  fn err_reader(& mut self) -> Option<& mut process::ChildStderr> {
    self.kid.stderr()
  }

  /** Gets the standard error output of the process as a string. */
  #[inline]
  pub fn out_as_string(& mut self) -> IoRes<String> {
    let mut s = String::new() ;
    match self.out_reader() {
      Some(stdout) => match stdout.read_to_string(& mut s) {
        Ok(_) => Ok(s),
        Err(e) => Err(e),
      },
      None => Err(
        io::Error::new(
          io::ErrorKind::Other, "cannot access stdout of child process"
        )
      ),
    }
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
  pub fn push(
    & mut self, n: & u8
  ) -> UnitSmtRes {
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
  pub fn pop(
    & mut self, n: & u8
  ) -> UnitSmtRes {
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
  pub fn reset_assertions(
    & mut self
  ) -> UnitSmtRes {
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
  pub fn declare_sort<Sort: PrintSmt2<()>>(
    & mut self, sort: Sort, arity: & u8
  ) -> UnitSmtRes {
    parse_success!(
      self for {
        let mut writer = try_writer!( self.writer() ) ;
        smt_cast_io!(
          write!(writer, "(declare-sort ") ;
          sort.to_smt2(writer, ()) ;
          write!(writer, " {})\n", arity)
        )
      }
    )
  }
  /** Defines a new sort. */
  #[inline]
  pub fn define_sort<Sort: PrintSmt2<()>, Expr: PrintSmt2<()>>(
    & mut self, sort: Sort, args: & [ Expr ], body: Expr
  ) -> UnitSmtRes {
    parse_success!(
      self for {
        let mut writer = try_writer!( self.writer() ) ;
        smtry_io!(
          write!(writer, "( define-sort ") ;
          sort.to_smt2(writer, ()) ;
          write!(writer, "\n   ( ")
        ) ;
        for arg in args {
          smtry_io!(
            arg.to_smt2(writer, ()) ;
            write!(writer, " ")
          ) ;
        } ;
        smt_cast_io!(
          write!(writer, ")\n   ") ;
          body.to_smt2(writer, ()) ;
          write!(writer, "\n)\n")
        )
      }
    )
  }
  /** Declares a new function symbol. */
  #[inline]
  pub fn declare_fun<
    IdentPrintInfo,
    Sort: PrintSmt2<()>, Ident: PrintSmt2<IdentPrintInfo>
  > (
    & mut self, symbol: & Ident, info: IdentPrintInfo,
    args: & [ Sort ], out: Sort
  ) -> UnitSmtRes {
    parse_success!(
      self for {
        let mut writer = try_writer!( self.writer() ) ;
        smtry_io!(
          write!(writer, "(declare-fun ") ;
          symbol.to_smt2(writer, info) ;
          write!(writer, " ( ")
        ) ;
        for arg in args {
          smtry_io!(
            arg.to_smt2(writer, ()) ;
            write!(writer, " ")
          ) ;
        } ;
        smt_cast_io!(
          write!(writer, ") ") ;
          out.to_smt2(writer, ()) ;
          write!(writer, ")\n")
        )
      }
    )
  }
  /** Declares a new function symbol, no info version. */
  #[inline(always)]
  pub fn ninfo_declare_fun<
    Sort: PrintSmt2<()>, Ident: PrintSmt2<()>
  > (
    & mut self, symbol: & Ident, args: & [ Sort ], out: Sort
  ) -> UnitSmtRes {
    self.declare_fun(symbol, (), args, out)
  }
  /** Declares a new constant. */
  #[inline]
  pub fn declare_const<Sort: PrintSmt2<()>, Ident: PrintSmt2<()>>(
    & mut self, symbol: Ident, out_sort: Sort
  ) -> UnitSmtRes {
    parse_success!(
      self for {
        let mut writer = try_writer!( self.writer() ) ;
        smt_cast_io!(
          write!(writer, "(declare-const ") ;
          symbol.to_smt2(writer, ()) ;
          write!(writer, " ") ;
          out_sort.to_smt2(writer, ()) ;
          write!(writer, ")\n")
        )
      }
    )
  }
  /** Defines a new function symbol. */
  #[inline]
  pub fn define_fun<
    Sort: PrintSmt2<()>, Ident: PrintSmt2<()>, Expr: PrintSmt2<()>
  >(
    & mut self,
    symbol: Ident, args: & [ (Ident, Sort) ], out: Sort, body: Expr
  ) -> UnitSmtRes {
    parse_success!(
      self for {
        let mut writer = try_writer!( self.writer() ) ;
        smtry_io!(
          write!(writer, "(define-fun ") ;
          symbol.to_smt2(writer, ()) ;
          write!(writer, " ( ")
        ) ;
        for arg in args {
          let (ref id, ref sort) = * arg ;
          smtry_io!(
            write!(writer, "(") ;
            id.to_smt2(writer, ()) ;
            write!(writer, " ") ;
            sort.to_smt2(writer, ()) ;
            write!(writer, ") ")
          )
        } ;
        smt_cast_io!(
          write!(writer, ") ") ;
          out.to_smt2(writer, ()) ;
          write!(writer, "\n   ") ;
          body.to_smt2(writer, ()) ;
          write!(writer, "\n)\n")
        )
      }
    )
  }
  /** Defines some new (possibily mutually) recursive functions. */
  #[inline]
  pub fn define_funs_rec<
    Sort: PrintSmt2<()>, Ident: PrintSmt2<()>, Expr: PrintSmt2<()>
  >(
    & mut self, funs: & [ (Ident, & [ (Ident, Sort) ], Sort, Expr) ]
  ) -> UnitSmtRes {
    parse_success!(
      self for {
        let mut writer = try_writer!( self.writer() ) ;
        // Header.
        smtry_io!( write!(writer, "(define-funs-rec (\n") ) ;

        // Signatures.
        for fun in funs {
          let (ref id, ref args, ref out, _) = * fun ;
          smtry_io!(
            write!(writer, "   (");
            id.to_smt2(writer, ()) ;
            write!(writer, " ( ")
          ) ;
          for arg in * args {
            let (ref arg, ref sort) = * arg ;
            smtry_io!(
              write!(writer, "(") ;
              arg.to_smt2(writer, ()) ;
              write!(writer, " ") ;
              sort.to_smt2(writer, ()) ;
              write!(writer, ") ")
            )
          } ;
          smtry_io!(
            write!(writer, ") ") ;
            out.to_smt2(writer, ()) ;
            write!(writer, ")\n")
          )
        } ;
        smtry_io!( write!(writer, " ) (") ) ;

        // Bodies
        for fun in funs {
          let (_, _, _, ref body) = * fun ;
          smtry_io!(
            write!(writer, "\n   ") ;
            body.to_smt2(writer, ())
          )
        } ;
        smt_cast_io!( write!(writer, "\n )\n)\n") )
      }
    )
  }
  /** Defines a new recursive function. */
  #[inline]
  pub fn define_fun_rec<
    Sort: PrintSmt2<()>, Ident: PrintSmt2<()>, Expr: PrintSmt2<()>
  >(
    & mut self,  symbol: Ident, args: & [ (Ident, Sort) ], out: Sort, body: Expr
  ) -> UnitSmtRes {
    parse_success!(
      self for {
        let mut writer = try_writer!( self.writer() ) ;
        // Header.
        smtry_io!( write!(writer, "(define-fun-rec (\n") ) ;

        // Signature.
        smtry_io!(
          write!(writer, "   (") ;
          symbol.to_smt2(writer, ()) ;
          write!(writer, " ( ")
        ) ;
        for arg in args {
          let (ref arg, ref sort) = * arg ;
          smtry_io!(
            write!(writer, "(") ;
            arg.to_smt2(writer, ()) ;
            write!(writer, " ") ;
            sort.to_smt2(writer, ()) ;
            write!(writer, ") ")
          )
        } ;
        smtry_io!(
          write!(writer, ") ") ;
          out.to_smt2(writer, ()) ;
          write!(writer, ")\n") ;
          write!(writer, " ) (")
        ) ;

        // Body.
        smt_cast_io!(
          write!(writer, "\n   ") ;
          body.to_smt2(writer, ()) ;
          write!(writer, "\n )\n)\n")
        )
      }
    )
  }


  // |===| Asserting and inspecting formulas.

  /** Asserts an expression with some print information. */
  #[inline]
  pub fn assert<PrintInfo, Expr: PrintSmt2<PrintInfo>>(
    & mut self, expr: & Expr, info: PrintInfo
  ) -> UnitSmtRes {
    parse_success!(
      self for {
        let mut writer = try_writer!( self.writer() ) ;
        smt_cast_io!(
          write!(writer, "(assert\n  ") ;
          expr.to_smt2(writer, info) ;
          write!(writer, "\n)\n")
        )
      }
    )
  }
  /** Asserts an expression without any print info. `ninfo` = no info. */
  #[inline(always)]
  pub fn ninfo_assert<Expr: PrintSmt2<()>>(
    & mut self, expr: & Expr
  ) -> UnitSmtRes {
    self.assert(expr, ())
  }
  /** Get assertions command. */
  #[inline]
  pub fn get_assertions(
    & mut self
  ) -> UnitSmtRes {
    let mut writer = try_writer!( self.writer() ) ;
    smt_cast_io!( write!(writer, "(get-assertions)\n") )
  }


  // |===| Checking for satisfiability.

  /** Check-sat command. */
  #[inline]
  pub fn check_sat(& mut self) -> UnitSmtRes {
    let mut writer = try_writer!( self.writer() ) ;
    smt_cast_io!( write!(writer, "(check-sat)\n") )
  }
  /** Check-sat assuming command. */
  #[inline]
  pub fn check_sat_assuming<PrintInfo: Copy, Ident: PrintSmt2<PrintInfo>>(
    & mut self, bool_vars: & [ Ident ], info: PrintInfo
  ) -> UnitSmtRes {
    match self.conf.get_check_sat_assuming() {
      & Ok(cmd) => {
        let mut writer = try_writer!( self.writer() ) ;
        smtry_io!( write!(writer, "({}\n ", cmd) );
        for v in bool_vars {
          smtry_io!(
            write!(writer, " ") ;
            v.to_smt2(writer, info)
          )
        } ;
        smt_cast_io!( write!(writer, "\n)\n") )
      },
      _ => panic!("check-sat-assuming command is not supported")
    }
  }
  /** Check-sat assuming command, no info version. */
  pub fn ninfo_check_sat_assuming<Ident: PrintSmt2<()>>(
    & mut self, bool_vars: & [ Ident ]
  ) -> UnitSmtRes {
    self.check_sat_assuming(bool_vars, ())
  }


  // |===| Inspecting models.

  /** Get value command. */
  #[inline]
  pub fn get_values<PrintInfo: Copy, Expr: PrintSmt2<PrintInfo>>(
    & mut self, exprs: & [ Expr ], info: PrintInfo
  ) -> UnitSmtRes {
    let mut writer = try_writer!( self.writer() ) ;
    smtry_io!( write!(writer, "(get-value (") ) ;
    for e in exprs {
      smtry_io!(
        write!(writer, "\n  ") ;
        e.to_smt2(writer, info)
      )
    } ;
    smt_cast_io!( write!(writer, "\n) )\n") )
  }
  /** Get value command, no info version. */
  #[inline(always)]
  pub fn ninfo_get_values<Expr: PrintSmt2<()>>(
    & mut self, exprs: & [ Expr]
  ) -> UnitSmtRes {
    self.get_values(exprs, ())
  }
  /** Get assignment command. */
  #[inline(always)]
  pub fn get_assignment(& mut self) -> UnitSmtRes {
    let mut writer = try_writer!( self.writer() ) ;
    smt_cast_io!( write!(writer, "(get-assignment)\n") )
  }
  /** Get model command. */
  #[inline(always)]
  pub fn get_model(& mut self) -> UnitSmtRes {
    let mut writer = try_writer!( self.writer() ) ;
    smt_cast_io!( write!(writer, "(get-model)\n") )
  }


  // |===| Inspecting proofs.

  /** Get unsat assumptions command. */
  #[inline(always)]
  pub fn get_unsat_assumptions(
    & mut self
  ) -> UnitSmtRes {
    let mut writer = try_writer!( self.writer() ) ;
    smt_cast_io!( write!(writer, "(get-unsat-assumptions)\n") )
  }
  /** Get proof command. */
  #[inline(always)]
  pub fn get_proof(
    & mut self
  ) -> UnitSmtRes {
    let mut writer = try_writer!( self.writer() ) ;
    smt_cast_io!( write!(writer, "(get-proof)\n") )
  }
  /** Get unsat core command. */
  #[inline(always)]
  pub fn get_unsat_core(
    & mut self
  ) -> UnitSmtRes {
    let mut writer = try_writer!( self.writer() ) ;
    smt_cast_io!( write!(writer, "(get-unsat-core)\n") )
  }

  // |===| Inspecting settings.

  /** Get info command. */
  #[inline(always)]
  pub fn get_info(
    & mut self, flag: & str
  ) -> UnitSmtRes {
    let mut writer = try_writer!( self.writer() ) ;
    smt_cast_io!( write!(writer, "(get-info {})\n", flag) )
  }
  /** Get option command. */
  #[inline(always)]
  pub fn get_option(
    & mut self, option: & str
  ) -> UnitSmtRes {
    let mut writer = try_writer!( self.writer() ) ;
    smt_cast_io!( write!(writer, "(get-option {})\n", option) )
  }

  // |===| Script information.

  /** Set info command. */
  #[inline(always)]
  pub fn set_info(
    & mut self, attribute: & str
  ) -> UnitSmtRes {
    let mut writer = try_writer!( self.writer() ) ;
    smt_cast_io!( write!(writer, "(set-info {})\n", attribute) )
  }
  /** Echo command. */
  #[inline(always)]
  pub fn echo(
    & mut self, text: & str
  ) -> UnitSmtRes {
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

  /** Parse the result of a check-sat. */
  #[inline]
  pub fn parse_check_sat(& mut self) -> CheckSatRes {
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

  /** Parser the result of a get-values. */
  #[inline]
  pub fn parse_values(& mut self) -> SmtRes<Vec<(
    Parser::Expr, Parser::Value
  )>> where Parser::Value: Debug, Parser::Expr: Debug {
    use nom::StepperState::* ;
    use parse::{ open_paren, close_paren, unexpected } ;
    let parser = & self.parser ;
    let mut stepper = stepper_of!(self.kid) ;

    /* Parse an error (done) or an opening parenthesis (values). */
    loop {
      match stepper.step (
        closure!(
          alt!(
            map!( unexpected, |e| Some(e) ) |
            map!( open_paren, |_| None )
          )
        )
      ) {
        Value( Some(err) ) => return Err(err),
        Value( None ) => break,
        ParserError(::nom::Err::Position(p,txt)) => {
          panic!("at {}: \"{}\"", p, ::std::str::from_utf8(txt).unwrap())
        },
        step => panic!("{:?}", step),
      }
    }

    let mut vec = vec![] ;

    loop {
      /* Parse an opening (value definition) or a closing (done) parenthesis.
      */
      match stepper.current_step(
        closure!(
          alt!(
            map!(open_paren, |_| false) | map!(close_paren, |_| true)
          )
        )
      ) {
        Value(closed) => if closed { return Ok(vec) },
        ParserError(::nom::Err::Position(p,txt)) => {
          panic!("at {}: \"{}\"", p, ::std::str::from_utf8(txt).unwrap())
        },
        step => panic!("{:?}", step),
      } ;
      /* We're parsing an expression/value pair. Parsing expr. */
      let expr = match stepper.current_step(|array| parser.parse_expr(array)) {
        Value(expr) => expr,
        ParserError(::nom::Err::Position(p,txt)) => {
          panic!("at {}: \"{}\"", p, ::std::str::from_utf8(txt).unwrap())
        },
        step => panic!("{:?}", step),
      } ;
      /* Parsing value. */
      let val = match stepper.current_step(|array| parser.parse_value(array)) {
        Value(value) => value,
        ParserError(::nom::Err::Position(p,txt)) => {
          panic!("at {}: \"{}\"", p, ::std::str::from_utf8(txt).unwrap())
        },
        step => panic!("{:?}", step),
      } ;
      /* End of expression/value pair. */
      match stepper.current_step(close_paren) {
        Value(_) => (),
        ParserError(::nom::Err::Position(p,txt)) => {
          panic!("at {}: \"{}\"", p, ::std::str::from_utf8(txt).unwrap())
        },
        step => panic!("{:?}", step),
      } ;
      /* Push on vector and loop. */
      vec.push((expr,val)) ;
    }
  }

  /** Parses the result of a get-model. */
  #[inline]
  pub fn parse_model(& mut self) -> SmtRes<Vec<(
    Parser::Ident, Parser::Value
  )>> where Parser::Value: Debug, Parser::Ident: Debug {
    use nom::StepperState::* ;
    use parse::{ open_paren, close_paren, unexpected } ;
    let parser = & self.parser ;
    let mut stepper = stepper_of!(self.kid) ;

    /* Parse an error (done) or an opening parenthesis (values). */
    loop {
      match stepper.step (
        closure!(
          alt!(
            map!( unexpected, |e| Some(e) ) |
            chain!(
              open_paren ~
              opt!(multispace) ~
              tag!("model"),
              || None
            )
          )
        )
      ) {
        Value( Some(err) ) => return Err(err),
        Value( None ) => break,
        Continue => continue,
        ParserError(::nom::Err::Position(p,txt)) => {
          panic!("at {}: \"{}\"", p, ::std::str::from_utf8(txt).unwrap())
        },
        step => panic!("{:?}", step),
      }
    }

    let mut vec = vec![] ;

    loop {
      /* Parse an opening (value definition) or a closing (done) parenthesis.
      */
      match stepper.current_step(
        closure!(
          alt!(
            chain!(
              open_paren ~
              opt!(multispace) ~
              tag!("define-fun"),
              || false
            ) |
            map!(close_paren, |_| true)
          )
        )
      ) {
        Value(closed) => if closed { return Ok(vec) },
        ParserError(::nom::Err::Position(p,txt)) => {
          panic!("at {}: \"{}\"", p, ::std::str::from_utf8(txt).unwrap())
        },
        step => panic!("{:?}", step),
      } ;
      /* We're parsing an ident/value pair. Parsing ident. */
      let ident = match stepper.current_step(
        |array| parser.parse_ident(array)
      ) {
        Value(ident) => ident,
        ParserError(::nom::Err::Position(p,txt)) => {
          panic!("at {}: \"{}\"", p, ::std::str::from_utf8(txt).unwrap())
        },
        step => panic!("{:?}", step),
      } ;
      /* Throwing away type info. */
      match stepper.current_step(
        closure!(
          chain!(
            opt!(multispace) ~
            char!('(') ~
            opt!(is_not!("()")) ~
            char!(')') ~
            opt!(multispace) ~
            is_not!(" \t\n") ~
            opt!(multispace),
            || ()
          )
        )
      ) {
        Value(_) => (),
        ParserError(::nom::Err::Position(p,txt)) => {
          panic!("at {}: \"{}\"", p, ::std::str::from_utf8(txt).unwrap())
        },
        step => panic!("{:?}", step),
      }
      /* Parsing value. */
      let val = match stepper.current_step(|array| parser.parse_value(array)) {
        Value(value) => value,
        ParserError(::nom::Err::Position(p,txt)) => {
          panic!("at {}: \"{}\"", p, ::std::str::from_utf8(txt).unwrap())
        },
        step => panic!("{:?}", step),
      } ;
      /* End of expression/value pair. */
      match stepper.current_step(close_paren) {
        Value(_) => (),
        ParserError(::nom::Err::Position(p,txt)) => {
          panic!("at {}: \"{}\"", p, ::std::str::from_utf8(txt).unwrap())
        },
        step => panic!("{:?}", step),
      } ;
      /* Push on vector and loop. */
      vec.push((ident,val)) ;
    }
  }
}



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


