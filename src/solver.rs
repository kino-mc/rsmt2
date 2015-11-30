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


use std::process::{ ChildStdin, Command, Stdio } ;
use std::fmt::Debug ;
use std::io ;
use std::io::{ Write, Read, BufWriter } ;
use std::fs::File ;
use std::process ;

use nom::{ multispace, IResult } ;

use common::* ;
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
            io::ErrorKind::Other, "cannot access writer of child process"
          )
        )
      ),
    }
  )
}

macro_rules! try_reader {
  ($e:expr) => (
    match $e {
      Some(reader) => reader,
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

#[cfg(not(no_parse_success))]
macro_rules! new_parse_success {
  ($slf:ident for $b:block) => (
    {
      let res = $b ;
      if $slf.conf().get_parse_success() {
        match $slf.parse_success() {
          Ok(()) => res,
          e => e
        }
      } else { res }
    }
  ) ;
}

#[cfg(no_parse_success)]
macro_rules! new_parse_success {
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


macro_rules! fetch {
  ($slf:expr, $start:expr, $c:ident => $action:expr) => ( {
    ::std::mem::swap(& mut $slf.buff, & mut $slf.swap) ;
    let mut buff = ::std::io::BufReader::new(
      try_reader!( $slf.kid.stdout() )
    ) ;
    let mut cnt = 0 ;
    let mut qid = false ;
    let mut str = false ;
    loop {
      use std::io::BufRead ;
      let len = $slf.buff.len() ;
      match buff.read_line(& mut $slf.buff) {
        Ok(_) => (),
        Err(e) => return Err( IOError(e) ),
      } ;
      let mut cmt = false ;
      if len < $slf.buff.len() {
        $start ;
        $slf.buff.trim_right() ;
        for $c in $slf.buff.chars().skip(len) {
          $action ;
          let normal = ! (qid || str || cmt) ;
          match $c {
            ';' if normal => cmt = true,
            '(' if normal => cnt += 1,
            ')' if normal => cnt -= 1,
            '|' if ! (str || cmt) => qid = ! qid,
            '"' if ! (qid || cmt) => str = ! str,
            _ => (),
          }
        }
      } ;
      if cnt == 0 { break }
    } ;
    Ok(())
  } ) ;
  ($slf:ident) => ( fetch!( $slf, (), c => () ) ) ;
}

macro_rules! parse {
  ($slf:expr, $fetch:expr, $parse:expr) => ( {
    use nom::IResult::* ;
    $fetch ;
    let res = match $parse {
      Done(rest, res) => {
        $slf.swap.clear() ;
        $slf.swap.extend(
          ::std::str::from_utf8(rest).unwrap().chars()
        ) ;
        res
      },
      Error(e) => return Err(
        UnexSmtRes::Error(format!("{:?}", e))
      ),
      Incomplete(n) => panic!("incomplete {:?}", n),
    } ;
    res
  } )
}

/** Contains an actual solver process. */
pub struct Solver<
  Parser: ParseSmt2
> {
  /** The command used to run the solver. */
  cmd: Command,
  /** The actual solver child process. */
  kid: Kid,
  /** Line buffer. */
  buff: String,
  /** Line swapper. */
  swap: String,
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
          cmd: cmd,
          kid: Kid::mk(kid),
          buff: String::with_capacity(1000),
          swap: String::with_capacity(1000),
          conf: conf,
          parser: parser,
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
  // fn reader(& mut self) -> Option<& mut process::ChildStdout> {
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

  /** Fetches data if necessary. */
  fn fetch(& mut self) -> UnitSmtRes {
    ::std::mem::swap(& mut self.buff, & mut self.swap) ;
    let mut buff = ::std::io::BufReader::new(
      try_reader!(self.kid.stdout())
    ) ;
    let mut cnt = 0 ;
    let mut qid = false ;
    let mut str = false ;
    loop {
      use std::io::BufRead ;
      let len = self.buff.len() ;
      match buff.read_line(& mut self.buff) {
        Ok(_) => (),
        Err(e) => return Err( UnexSmtRes::IOError(e) ),
      } ;
      if len < self.buff.len() {
        self.buff.trim_right() ;
        for c in self.buff.chars().skip(len) {
          let normal = ! (qid || str) ;
          match c {
            '(' if normal => cnt += 1,
            ')' if normal => cnt -= 1,
            '|' if !str => qid = ! qid,
            '"' if !qid => str = ! str,
            _ => (),
          }
        } ;
        if cnt == 0 { break }
      }
    }
    Ok(())
  }

  /** Applies a parser and returns its result. Fetches more data if necessary.
  */
  fn parse<'a, T, F: Fn(& 'a [u8]) -> IResult<& 'a [u8], SmtRes<T>>>(
    & 'a mut self, parser: F
  ) -> SmtRes<T> {
    use nom::IResult::* ;
    try!( self.fetch() ) ;
    let res = match parser( self.buff.as_ref() ) {
      Done(rest, res) => {
        self.swap.clear() ;
        self.swap.extend( ::std::str::from_utf8(rest).unwrap().chars() ) ;
        res
      },
      Error(e) => return Err( UnexSmtRes::Error(format!("{:?}", e)) ),
      Incomplete(n) => panic!("incomplete {:?}", n),
    } ;
    res
  }

  /** Applies a parser and returns its result. Fetches more data if necessary.
  Gives the internal parser as parameter to the parser. */
  fn cstm_parse<
    'a, T, F: Fn(& 'a [u8], & Parser) -> IResult<& 'a [u8], SmtRes<T>>
  >(& 'a mut self, parser: F) -> SmtRes<T> {
    use nom::IResult::* ;
    try!( self.fetch() ) ;
    let res = match parser( self.buff.as_ref(), & self.parser ) {
      Done(rest, res) => {
        self.swap.clear() ;
        self.swap.extend( ::std::str::from_utf8(rest).unwrap().chars() ) ;
        res
      },
      Error(e) => return Err( UnexSmtRes::Error(format!("{:?}", e)) ),
      Incomplete(n) => panic!("incomplete {:?}", n),
    } ;
    res
  }

  /** Parse success. */
  #[inline]
  fn parse_success(& mut self) -> SuccessRes {
    self.parse(success)
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
    self.parse(check_sat)
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
    use parse::{ open_paren, close_paren, unexpected } ;

    self.cstm_parse(|bytes, parser|
      call!(bytes,
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
                  alt!(
                    tag!("Bool") | tag!("Int") | tag!("Real") |
                    tag!("bool") | tag!("int") | tag!("real")
                  ) ~
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
      )
    )
  }


  /** Parser the result of a get-values. */
  #[inline]
  fn parse_values(& mut self, info: & Parser::I) -> SmtRes<
    Vec<(Parser::Expr, Parser::Value)>
  > {
    use parse::{ open_paren, close_paren, unexpected } ;

    self.cstm_parse(
      |bytes, parser| call!(bytes,
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
      )
    )
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





/** Contains an actual solver process. */
pub struct NormalSolver<
  Parser: ParseSmt2
> {
  /** The command used to run the solver. */
  cmd: Command,
  /** The actual solver child process. */
  kid: Kid,
  /** Line buffer. */
  buff: String,
  /** Line swapper. */
  swap: String,
  /** The solver specific information. */
  conf: SolverConf,
  /** The parser. */
  parser: Parser,
}

impl<Parser: ParseSmt2> NormalSolver<Parser> {
  /** Creates a solver logging commands and results in a file. */
  pub fn tee(
    self, log: & ::std::path::Path
  ) -> SmtRes<TeeSolver<Parser>> {
    use std::fs::OpenOptions ;
    match OpenOptions::new().write(true).open(log) {
      Ok(file) => Ok(
        TeeSolver { solver: self, file: file }
      ),
      Err(e) => Err(
        Error(
          format!("could not open log file \"{:?}\": {}", log, e)
        )
      ),
    }
  }

  /** Fetches data if necessary. */
  fn fetch(& mut self) -> UnitSmtRes {
    fetch!(self)
  }
}




impl<Parser: ParseSmt2>
SolverPrimitives<Parser> for
NormalSolver<Parser> {
  fn conf(& self) -> & SolverConf { & self.conf }
  fn stop(self) -> IoRes<(Command, SolverConf)> {
    let (cmd,conf,kid) = (self.cmd, self.conf, self.kid) ;
    match kid.kill() {
      Ok(()) => Ok((cmd, conf)),
      Err(e) => Err(e)
    }
  }
  fn write<
    T, F: Fn(& mut Write) -> SmtRes<T>
  >(& mut self, f: F) -> SmtRes<T> {
    match self.kid.stdin() {
      Some(stdin) => f(
        & mut BufWriter::with_capacity(1000, stdin)
      ),
      None => Err(
        Error("could not access stdin of solver".to_string())
      ),
    }
  }
  fn parse<'a, T, F: Fn(& 'a [u8]) -> IResult<& 'a [u8], SmtRes<T>>>(
    & 'a mut self, parser: F
  ) -> SmtRes<T> {
    parse!(
      self, try!( self.fetch() ), parser( self.buff.as_ref() )
    )
  }
  fn cstm_parse<
    'a, T, F: Fn(& 'a [u8], & Parser) -> IResult<& 'a [u8], SmtRes<T>>
  >(& 'a mut self, parser: F) -> SmtRes<T> {
    parse!(
      self, try!( self.fetch() ),
      parser( self.buff.as_ref(), & self.parser )
    )
  }
}

impl<Parser: ParseSmt2> SolverCmd<Parser> for NormalSolver<Parser> {}




/** Contains an actual solver process. */
pub struct TeeSolver<
  Parser: ParseSmt2
> {
  /** The actual solver. */
  solver: NormalSolver<Parser>,
  /** The file we're logging to. */
  file: File,
}

impl<Parser: ParseSmt2> TeeSolver<Parser> {
  /** Fetches data if necessary. */
  fn fetch(& mut self) -> UnitSmtRes {
    fetch!(
      self.solver,
      smtry_io!( write!(self.file, ";; ") ),
      c => smtry_io!( write!(self.file, "{}", c) )
    )
  }
}




/** Tee writer. */
struct TeeWriter<W1: Write, W2: Write> {
  w1: W1, w2: W2
}
impl<W1: Write, W2: Write> TeeWriter<W1, W2> {
  fn mk(w1: W1, w2: W2) -> BufWriter<Self> {
    BufWriter::with_capacity(
      1000, TeeWriter { w1: w1, w2: w2 }
    )
  }
}
impl<W1: Write, W2: Write> Write for TeeWriter<W1, W2> {
  fn write(& mut self, buf: & [u8]) -> IoRes<usize> {
    try!( self.w1.write(buf) ) ;
    self.w2.write(buf)
  }
  fn flush(& mut self) -> IoRes<()> {
    try!( self.w1.flush() ) ;
    self.w2.flush()
  }
}


impl<Parser: ParseSmt2>
SolverPrimitives<Parser> for
TeeSolver<Parser> {
  fn conf(& self) -> & SolverConf { self.solver.conf() }
  fn stop(self) -> IoRes<(Command, SolverConf)> { self.solver.stop() }
  fn write<
    T, F: Fn(& mut Write) -> SmtRes<T>
  >(& mut self, f: F) -> SmtRes<T> {
    match self.solver.kid.stdin() {
      Some(stdin) => f(
        & mut TeeWriter::mk(stdin, & mut self.file)
      ),
      None => Err(
        Error("could not access stdin of solver".to_string())
      ),
    }
  }
  fn parse<'a, T, F: Fn(& 'a [u8]) -> IResult<& 'a [u8], SmtRes<T>>>(
    & 'a mut self, parser: F
  ) -> SmtRes<T> {
    parse!(
      self.solver, try!( self.fetch() ), parser( self.solver.buff.as_ref() )
    )
  }
  fn cstm_parse<
    'a, T, F: Fn(& 'a [u8], & Parser) -> IResult<& 'a [u8], SmtRes<T>>
  >(& 'a mut self, parser: F) -> SmtRes<T> {
    parse!(
      self.solver, try!( self.fetch() ),
      parser( self.solver.buff.as_ref(), & self.solver.parser )
    )
  }
}

impl<Parser: ParseSmt2> SolverCmd<Parser> for TeeSolver<Parser> {}


/** Primitive functions provided by a solver wrapper. */
trait SolverPrimitives<Parser: ParseSmt2> {
  /** The configuration of the solver. */
  #[inline(always)]
  fn conf(& self) -> & SolverConf ;

  /** Kills the underlying solver. */
  #[inline(always)]
  fn stop(self) -> IoRes<(Command, SolverConf)> ;

  /** Writes something on solver's stdin. */
  #[inline(always)]
  fn write<
    T, F: Fn(& mut Write) -> SmtRes<T>
  >(& mut self, f: F) -> SmtRes<T> ;

  /** Applies a parser and returns its result. Fetches more data if necessary.
  */
  fn parse<'a, T, F: Fn(& 'a [u8]) -> IResult<& 'a [u8], SmtRes<T>>>(
    & 'a mut self, parser: F
  ) -> SmtRes<T> ;

  /** Applies a parser and returns its result. Fetches more data if necessary.
  Gives the internal parser as parameter to the parser. */
  fn cstm_parse<
    'a, T, F: Fn(& 'a [u8], & Parser) -> IResult<& 'a [u8], SmtRes<T>>
  >(& 'a mut self, parser: F) -> SmtRes<T> ;
}



pub trait SolverCmd<Parser: ParseSmt2> : Sized + SolverPrimitives<Parser> {

  /** Creates a solver. */
  fn mk(
    cmd: Command, conf: SolverConf, parser: Parser
  ) -> SmtRes<NormalSolver<Parser>> {
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
        let mut solver = NormalSolver {
          cmd: cmd,
          kid: Kid::mk(kid),
          buff: String::with_capacity(1000),
          swap: String::with_capacity(1000),
          conf: conf,
          parser: parser,
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
  fn kill(self) -> IoRes<(Command, SolverConf)> { self.stop() }


  // Comment things.

  /** Prints some text as comments. Input is sanitized in case it contains
  newlines. */
  #[inline(always)]
  fn comment(& mut self, txt: & str) -> UnitSmtRes {
    self.write(
      |w| {
        for line in txt.lines() {
          smtry_io!( write!(w, ";; {}\n", line) )
        } ;
        smt_cast_io!( write!(w, "\n") )
      }
    )
  }


  // |===| (Re)starting and terminating.

  /** Resets the underlying solver. Restarts the kid process if no reset
  command is supported. */
  #[inline(always)]
  fn reset(
    & mut self
  ) -> UnitSmtRes {
    self.write(
      |w| smt_cast_io!( write!(w, "(reset)\n") )
    )
  }
  #[inline]
  /** Sets the logic. */
  fn set_logic(
    & mut self, logic: & Logic
  ) -> UnitSmtRes {
    new_parse_success!(
      self for {
        self.write(
          |w| smt_cast_io!(
            write!(w, "(set-logic ") ;
            logic.to_smt2(w, ()) ;
            write!(w, ")\n")
          )
        )
      }
    )
  }
  /** Set option command. */
  #[inline]
  fn set_option<Value: ::std::fmt::Display>(
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
    new_parse_success!(
      self for {
        self.write(
          |w| smt_cast_io!(
            write!(w, "(set-option {} {})\n", option, value)
          )
        )
      }
    )
  }
  /** Activates interactive mode. */
  #[inline(always)]
  fn interactive_mode(& mut self) -> UnitSmtRes {
    new_parse_success!(
      self for {
        self.write(
          |w| smt_cast_io!(
            write!(w, "(set-option :interactive-mode true)\n")
          )
        )
      }
    )
  }
  /** Activates print success. */
  #[inline(always)]
  fn print_success(& mut self) -> UnitSmtRes {
    new_parse_success!(
      self for {
        self.write(
          |w| smt_cast_io!(
            write!(w, "(set-option :print-success true)\n")
          )
        )
      }
    )
  }
  /** Activates unsat core production. */
  #[inline(always)]
  fn produce_unsat_core(& mut self) -> UnitSmtRes {
    new_parse_success!(
      self for {
        self.write(
          |w| smt_cast_io!(
            write!(w, "(set-option :produce-unsat-cores true)\n")
          )
        )
      }
    )
  }
  /** Shuts the solver down. */
  #[inline(always)]
  fn exit(& mut self) -> UnitSmtRes {
    new_parse_success!(
      self for {
        self.write(
          |w| smt_cast_io!(
            write!(w, "(exit)\n")
          )
        )
      }
    )
  }


  // |===| Modifying the assertion stack.

  /** Pushes `n` layers on the assertion stack. */
  #[inline(always)]
  fn push(& mut self, n: & u8) -> UnitSmtRes {
    new_parse_success!(
      self for {
        self.write(
          |w| smt_cast_io!(
            write!(w, "(push {})\n", n)
          )
        )
      }
    )
  }
  /** Pops `n` layers off the assertion stack. */
  #[inline(always)]
  fn pop(& mut self, n: & u8) -> UnitSmtRes {
    new_parse_success!(
      self for {
        self.write(
          |w| smt_cast_io!(
            write!(w, "(pop {})\n", n)
          )
        )
      }
    )
  }
  /** Resets the assertions in the solver. */
  #[inline(always)]
  fn reset_assertions(& mut self) -> UnitSmtRes {
    new_parse_success!(
      self for {
        self.write(
          |w| smt_cast_io!(
            write!(w, "(reset-assertions)\n")
          )
        )
      }
    )
  }


  // |===| Introducing new symbols.

  /** Declares a new sort. */
  #[inline]
  fn declare_sort<Sort: Sort2Smt>(
    & mut self, sort: & Sort, arity: & u8
  ) -> UnitSmtRes {
    new_parse_success!(
      self for {
        self.write(
          |w| smt_cast_io!(
            write!(w, "(declare-sort ") ;
            sort.sort_to_smt2(w) ;
            write!(w, " {})\n", arity)
          )
        )
      }
    )
  }
  /** Defines a new sort. */
  #[inline]
  fn define_sort<
    Sort: Sort2Smt, I, Expr1: Expr2Smt<I>, Expr2: Expr2Smt<I>
  >(
    & mut self, sort: & Sort, args: & [ Expr1 ], body: & Expr2, info: & I
  ) -> UnitSmtRes {
    new_parse_success!(
      self for {
        self.write(
          |w| {
            smtry_io!(
              write!(w, "( define-sort ") ;
              sort.sort_to_smt2(w) ;
              write!(w, "\n   ( ")
            ) ;
            for arg in args {
              smtry_io!(
                arg.expr_to_smt2(w, info) ;
                write!(w, " ")
              ) ;
            } ;
            smt_cast_io!(
              write!(w, ")\n   ") ;
              body.expr_to_smt2(w, info) ;
              write!(w, "\n)\n")
            )
          }
        )
      }
    )
  }
  /** Declares a new function symbol. */
  #[inline]
  fn declare_fun<Sort: Sort2Smt, I, Sym: Sym2Smt<I>> (
    & mut self, symbol: & Sym, args: & [ Sort ], out: & Sort, info: & I
  ) -> UnitSmtRes {
    new_parse_success!(
      self for {
        self.write(
          |w| {
            smtry_io!(
              write!(w, "(declare-fun ") ;
              symbol.sym_to_smt2(w, info) ;
              write!(w, " ( ")
            ) ;
            for arg in args {
              smtry_io!(
                arg.sort_to_smt2(w) ;
                write!(w, " ")
              ) ;
            } ;
            smt_cast_io!(
              write!(w, ") ") ;
              out.sort_to_smt2(w) ;
              write!(w, ")\n")
            )
          }
        )
      }
    )
  }
  /** Declares a new constant. */
  #[inline]
  fn declare_const<Sort: Sort2Smt, I, Sym: Sym2Smt<I>> (
    & mut self, symbol: & Sym, out_sort: & Sort, info: & I
  ) -> UnitSmtRes {
    new_parse_success!(
      self for {
        self.write(
          |w| smt_cast_io!(
            write!(w, "(declare-const ") ;
            symbol.sym_to_smt2(w, info) ;
            write!(w, " ") ;
            out_sort.sort_to_smt2(w) ;
            write!(w, ")\n")
          )
        )
      }
    )
  }
  /** Defines a new function symbol. */
  #[inline]
  fn define_fun<
    I, Sort: Sort2Smt, Sym1: Sym2Smt<I>, Sym2: Sym2Smt<I>, Expr: Expr2Smt<I>
  >(
    & mut self, symbol: & Sym1, args: & [ (Sym2, Sort) ],
    out: & Sort, body: & Expr, info: & I
  ) -> UnitSmtRes {
    new_parse_success!(
      self for {
        self.write(
          |w| {
            smtry_io!(
              write!(w, "(define-fun ") ;
              symbol.sym_to_smt2(w, info) ;
              write!(w, " ( ")
            ) ;
            for arg in args {
              let (ref sym, ref sort) = * arg ;
              smtry_io!(
                write!(w, "(") ;
                sym.sym_to_smt2(w, info) ;
                write!(w, " ") ;
                sort.sort_to_smt2(w) ;
                write!(w, ") ")
              )
            } ;
            smt_cast_io!(
              write!(w, ") ") ;
              out.sort_to_smt2(w) ;
              write!(w, "\n   ") ;
              body.expr_to_smt2(w, info) ;
              write!(w, "\n)\n")
            )
          }
        )
      }
    )
  }
  /** Defines some new (possibily mutually) recursive functions. */
  #[inline]
  fn define_funs_rec<
    I, Sort: Sort2Smt, Sym: Sym2Smt<I>, Expr: Expr2Smt<I>
  >(
    & mut self, funs: & [ (Sym, & [ (Sym, Sort) ], Sort, Expr) ], info: & I
  ) -> UnitSmtRes {
    new_parse_success!(
      self for {
        self.write(
          |w| {
            // Header.
            smtry_io!( write!(w, "(define-funs-rec (\n") ) ;

            // Signatures.
            for fun in funs {
              let (ref sym, ref args, ref out, _) = * fun ;
              smtry_io!(
                write!(w, "   (");
                sym.sym_to_smt2(w, info) ;
                write!(w, " ( ")
              ) ;
              for arg in * args {
                let (ref sym, ref sort) = * arg ;
                smtry_io!(
                  write!(w, "(") ;
                  sym.sym_to_smt2(w, info) ;
                  write!(w, " ") ;
                  sort.sort_to_smt2(w) ;
                  write!(w, ") ")
                )
              } ;
              smtry_io!(
                write!(w, ") ") ;
                out.sort_to_smt2(w) ;
                write!(w, ")\n")
              )
            } ;
            smtry_io!( write!(w, " ) (") ) ;

            // Bodies
            for fun in funs {
              let (_, _, _, ref body) = * fun ;
              smtry_io!(
                write!(w, "\n   ") ;
                body.expr_to_smt2(w, info)
              )
            } ;
            smt_cast_io!( write!(w, "\n )\n)\n") )
          }
        )
      }
    )
  }
  /** Defines a new recursive function. */
  #[inline]
  fn define_fun_rec<
    I, Sort: Sort2Smt, Sym: Sym2Smt<I>, Expr: Expr2Smt<I>
  >(
    & mut self,  symbol: & Sym, args: & [ (Sym, Sort) ],
    out: & Sort, body: & Expr, info: & I
  ) -> UnitSmtRes {
    new_parse_success!(
      self for {
        self.write(
          |w| {
            // Header.
            smtry_io!( write!(w, "(define-fun-rec (\n") ) ;

            // Signature.
            smtry_io!(
              write!(w, "   (") ;
              symbol.sym_to_smt2(w, info) ;
              write!(w, " ( ")
            ) ;
            for arg in args {
              let (ref sym, ref sort) = * arg ;
              smtry_io!(
                write!(w, "(") ;
                sym.sym_to_smt2(w, info) ;
                write!(w, " ") ;
                sort.sort_to_smt2(w) ;
                write!(w, ") ")
              )
            } ;
            smtry_io!(
              write!(w, ") ") ;
              out.sort_to_smt2(w) ;
              write!(w, ")\n") ;
              write!(w, " ) (")
            ) ;

            // Body.
            smt_cast_io!(
              write!(w, "\n   ") ;
              body.expr_to_smt2(w, info) ;
              write!(w, "\n )\n)\n")
            )
          }
        )
      }
    )
  }


  // |===| Asserting and inspecting formulas.

  /** Asserts an expression with some print information. */
  #[inline]
  fn assert<I, Expr: Expr2Smt<I>>(
    & mut self, expr: & Expr, info: & I
  ) -> UnitSmtRes {
    new_parse_success!(
      self for {
        self.write(
          |w| smt_cast_io!(
            write!(w, "(assert\n  ") ;
            expr.expr_to_smt2(w, info) ;
            write!(w, "\n)\n")
          )
        )
      }
    )
  }

  // |===| Inspecting settings.

  /** Get info command. */
  #[inline(always)]
  fn get_info(& mut self, flag: & str) -> UnitSmtRes {
    self.write(
      |w| smt_cast_io!( write!(w, "(get-info {})\n", flag) )
    )
  }
  /** Get option command. */
  #[inline(always)]
  fn get_option(& mut self, option: & str) -> UnitSmtRes {
    self.write(
      |w| smt_cast_io!( write!(w, "(get-option {})\n", option) )
    )
  }

  // |===| Script information.

  /** Set info command. */
  #[inline(always)]
  fn set_info(& mut self, attribute: & str) -> UnitSmtRes {
    self.write(
      |w| smt_cast_io!( write!(w, "(set-info {})\n", attribute) )
    )
  }
  /** Echo command. */
  #[inline(always)]
  fn echo(& mut self, text: & str) -> UnitSmtRes {
    self.write(
      |w| smt_cast_io!( write!(w, "(echo \"{}\")\n", text) )
    )
  }


  // |===| Parsing simple stuff.

  /** Parse success. */
  #[inline]
  fn parse_success(& mut self) -> SuccessRes {
    self.parse(success)
  }
}