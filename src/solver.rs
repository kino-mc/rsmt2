// See the LICENSE files at the top-level directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Wrapper around an SMT Lib 2 compliant solver.
//!
//! The underlying solver runs in a separate process, communication uses system
//! pipes.

use std::fs::File ;
use std::process::{
  Child, ChildStdin, ChildStdout, Command, Stdio
} ;
use std::io::{ Write, BufWriter, BufReader } ;

use nom::multispace ;

use errors::* ;

use common::* ;
use conf::SolverConf ;
use parse::{
  success, check_sat, unexpected, open_paren, close_paren
} ;


macro_rules! stutter_arg {
  ($slf:ident . $fun:ident ; $arg:expr) => (
    $slf.$fun($arg, $arg)
  ) ;
}


macro_rules! wrap {
  ($e:expr) => (
    {
      use nom::IResult::* ;
      use std::str::from_utf8 ;
      match $e {
        Done(rest, res) => match from_utf8(rest) {
          Ok(s) => (s.to_string(), res),
          Err(e) => (
            String::new(),
            Err(e).chain_err::<_, ErrorKind>(
              || "could not convert remaining bytes to utf8".into()
            )
          ),
        },
        Error(e) => (
          String::new(), Err(
            ErrorKind::ParseError(
              ::nom::IError::Error(e)
            ).into()
          )
        ),
        Incomplete(e) => (
          String::new(), Err(
            ErrorKind::ParseError(
              ::nom::IError::Incomplete(e)
            ).into()
          )
        ),
      }
    }
  )
}

#[cfg(not(no_parse_success))]
macro_rules! parse_success {
  ($slf:ident for $b:block) => (
    {
      let res = $b ;
      if $slf.solver().conf.get_parse_success() {
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

/// Macro for fetching data from the kid's output.
macro_rules! fetch {
  ($slf:expr, $start:expr, $c:ident => $action:expr) => ( {
    ::std::mem::swap(& mut $slf.buff, & mut $slf.swap) ;
    let mut buff = & mut $slf.stdout ;
    let mut cnt = 0 ;
    let mut qid = false ;
    let mut str = false ;
    loop {
      use std::io::BufRead ;
      let len = $slf.buff.len() ;
      buff.read_line(& mut $slf.buff) ? ;
      let mut cmt = false ;
      if len + 1 < $slf.buff.len() {
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
        } ;
        if cnt == 0 { break }
      } ;
    } ;
    Ok(())
  } ) ;
  ($slf:ident) => ( fetch!( $slf, (), c => () ) ) ;
}






/// A solver `Child`.
pub struct Kid {
  kid: Child,
  conf: SolverConf,
}
impl Kid {
  /// Creates a new solver kid.
  pub fn new(conf: SolverConf) -> Res<Self> {
    // Constructing command and spawning kid.
    Command::new(
      // Command.
      conf.get_cmd()
    ).args(
      // Options.
      conf.get_options()
    ).stdin(
      Stdio::piped()
    ).stdout(
      Stdio::piped()
    ).stderr(
      Stdio::piped()
    ).spawn().map(
      |kid| Kid {
        kid: kid,
        conf: conf,
      }
    ).chain_err::<_, ErrorKind>(
      || "while spawning child process".into()
    )
  }
  /// Kills the solver kid.
  pub fn kill(mut self) -> Res<()> {
    self.kid.kill().chain_err::<_, ErrorKind>(
      || "while killing child process".into()
    )
  }
}







/// Plain solver, as opposed to `TeeSolver` which logs IOs.
pub struct PlainSolver<'kid, Parser: ParseSmt2 + 'static> {
  /// Solver configuration.
  conf: & 'kid SolverConf,
  /// Kid's stdin.
  stdin: BufWriter<& 'kid mut ChildStdin>,
  /// Kid's stdout.
  stdout: BufReader<& 'kid mut ChildStdout>,
  // /// Kid's stderr.
  // stderr: BufReader<& 'kid mut ChildStderr>,
  /// Line buffer for the kid's output.
  buff: String,
  /// Line swapper.
  swap: String,
  /// User-provided parser.
  parser: Parser,
}
impl<'kid, Parser: ParseSmt2 + 'static> PlainSolver<'kid, Parser> {
  /// Creates a plain solver.
  pub fn new(kid: & 'kid mut Kid, parser: Parser) -> Res<Self> {
    let stdin = match kid.kid.stdin.as_mut() {
      Some(stdin) => BufWriter::with_capacity(1000, stdin),
      None => bail!(
        ErrorKind::IoError("could not access stdin of solver kid".into())
      ),
    } ;
    let stdout = match kid.kid.stdout.as_mut() {
      Some(stdout) => BufReader::with_capacity(1000, stdout),
      None => bail!(
        ErrorKind::IoError("could not access stdout of solver kid".into())
      ),
    } ;
    // let stderr = match kid.kid.stderr.as_mut() {
    //   Some(stderr) => BufReader::with_capacity(1000, stderr),
    //   None => return Err(
    //     Error("could not access stderr of solver kid".to_string())
    //   ),
    // } ;
    let mut solver = PlainSolver {
      conf: & kid.conf,
      stdin: stdin,
      stdout: stdout,
      // stderr: stderr,
      buff: String::with_capacity(1000),
      swap: String::with_capacity(1000),
      parser: parser,
    } ;
    if solver.conf.get_parse_success() {
      // Function `print_success` parses its own success.
      try!( solver.print_success() )
    } ;
    Ok(solver)
  }

  /// Wraps a solver to log IOs to a file.
  pub fn tee(
    self, file: File
  ) -> TeeSolver<'kid, Parser> {
    TeeSolver {
      solver: self, file: BufWriter::with_capacity(1000, file)
    }
  }

  /// Configuration of the solver.
  pub fn conf(& self) -> & SolverConf { self.conf }
}

impl<
  'kid, Parser: ParseSmt2 + 'static
> SolverBasic<'kid, Parser> for PlainSolver<'kid, Parser> {
  fn fetch(& mut self) -> Res<()> {
    fetch!(self)
  }
  fn write<
    F: Fn(& mut BufWriter<& mut ChildStdin>) -> Res<()>,
    FTee: Fn(& mut BufWriter<File>) -> Res<()>,
  >(& mut self, f: F, _: FTee) -> Res<()> {
    try!( f(& mut self.stdin) ) ;
    self.stdin.flush() ? ;
    Ok(())
  }
  fn comment(& mut self, _: & str) -> Res<()> {
    Ok(())
  }
  fn parser(& self) -> & Parser {
    & self.parser
  }
  fn as_ref(& self) -> & [u8] {
    self.buff.as_ref()
  }
  fn solver(& mut self) -> & mut PlainSolver<'kid, Parser> {
    self
  }
}

impl<
  'kid, Parser: ParseSmt2 + 'static
> SolverPrims<'kid, Parser> for PlainSolver<'kid, Parser> {}

impl<
  'kid, Parser: ParseSmt2 + 'static
> Solver<'kid, Parser> for PlainSolver<'kid, Parser> {}












/// Wrapper around a `PlainSolver` logging IOs to a file.
pub struct TeeSolver<'kid, Parser: ParseSmt2 + 'static> {
  solver: PlainSolver<'kid, Parser>,
  file: BufWriter<File>,
}
impl<'kid, Parser: ParseSmt2 + 'static> TeeSolver<'kid, Parser> {
  /// Configuration of the solver.
  pub fn conf(& self) -> & SolverConf { self.solver.conf }
}

impl<
  'kid, Parser: ParseSmt2 + 'static
> SolverBasic<'kid, Parser> for TeeSolver<'kid, Parser> {
  fn fetch(& mut self) -> Res<()> {
    fetch!(
      self.solver,
      write!(self.file, ";; ") ?,
      c => {
        write!( self.file, "{}", c) ?
      }
    )
  }
  /// Applies a function to the writer on the solver's stdin.
  fn write<
    F: Fn(& mut BufWriter<& mut ChildStdin>) -> Res<()>,
    FTee: Fn(& mut BufWriter<File>) -> Res<()>,
  >(& mut self, f: F, f_tee: FTee) -> Res<()> {
    try!( f(& mut self.solver.stdin) ) ;
    self.solver.stdin.flush() ? ;
    write_str(& mut self.file, "\n") ? ;
    f_tee(& mut self.file) ? ;
    self.file.flush() ? ;
    Ok(())
  }
  fn comment(& mut self, txt: & str) -> Res<()> {
    for line in txt.lines() {
      write!(self.file, "\n;; {}", line) ?
    }
    Ok(())
  }
  fn parser(& self) -> & Parser {
    & self.solver.parser
  }
  fn as_ref(& self) -> & [u8] {
    & self.solver.buff.as_ref()
  }
  fn solver(& mut self) -> & mut PlainSolver<'kid, Parser> {
    & mut self.solver
  }
}

impl<
  'kid, Parser: ParseSmt2 + 'static
> SolverPrims<'kid, Parser> for TeeSolver<'kid, Parser> {}

impl<
  'kid, Parser: ParseSmt2 + 'static
> Solver<'kid, Parser> for TeeSolver<'kid, Parser> {}













/// Most basic function needed to provide SMT-LIB commands.
pub trait SolverBasic<'kid, Parser: ParseSmt2 + 'static> {
  /// Fetches data.
  fn fetch(& mut self) -> Res<()> ;
  /// Applies a function to the writer on the solver's stdin.
  fn write<
    F: Fn(& mut BufWriter<& mut ChildStdin>) -> Res<()>,
    FTee: Fn(& mut BufWriter<File>) -> Res<()>,
  >(& mut self, f: F, f_tee: FTee) -> Res<()> ;
  /// Writes comments. Ignored for `PlainSolver`.
  fn comment(& mut self, txt: & str) -> Res<()> ;
  /// The bytes of the buffer.
  fn as_ref(& self) -> & [u8] ;
  /// The parser.
  fn parser(& self) -> & Parser ;
  /// The plain solver.
  fn solver(& mut self) -> & mut PlainSolver<'kid, Parser> ;
}













/// Primitive functions provided by a solver wrapper.
pub trait SolverPrims<
  'kid, Parser: ParseSmt2 + 'static
> : SolverBasic<'kid, Parser> {
  /// Fetchs data, applies a parser (passes the internal parser) and returns
  /// its result.
  fn parse<
    Out, F: Fn(& [u8], & Parser) -> (String, Res<Out>)
  >(& mut self, parser: F) -> Res<Out> {
    try!( self.fetch() ) ;
    let (rest, res) = parser( self.as_ref(), self.parser() ) ;
    let solver = self.solver() ;
    solver.swap.clear() ;
    solver.swap.extend( rest.chars() ) ;
    res
  }
}







/// Creates a solver from a kid.
pub fn solver<'kid, Parser: ParseSmt2 + 'static>(
  kid: & 'kid mut Kid, parser: Parser
) -> Res< PlainSolver<'kid, Parser> > {
  PlainSolver::new(kid, parser)
}







/// Provides SMT-LIB commands.
pub trait Solver<'kid, Parser: ParseSmt2 + 'static> :
SolverPrims<'kid, Parser> {


  // |===| (Re)starting and terminating.

  /// Resets the underlying solver. Restarts the kid process if no reset
  /// command is supported.
  #[inline(always)]
  fn reset(
    & mut self
  ) -> Res<()> {
    parse_success!(
      self for {
        stutter_arg!(
          self.write ; |w| write_str(w, "(reset)\n")
        )
      }
    )
  }



  /// Sets the logic.
  #[inline]
  fn set_logic(
    & mut self, logic: & Logic
  ) -> Res<()> {
    parse_success!(
      self for {
        stutter_arg!(
          self.write ; |w| {
            write_str(w, "(set-logic ") ? ;
            logic.to_smt2(w, ()) ? ;
            write_str(w, ")\n")
          }
        )
      }
    )
  }
  /// Set option command.
  #[inline]
  fn set_option<Value: ::std::fmt::Display>(
    & mut self, option: & str, value: Value
  ) -> Res<()> {
    match option {
      ":interactive_mode" => return Err(
        "illegal set-option on interactive mode".into()
      ),
      ":print_success" => return Err(
        "illegal set-option on print success, \
        use `SmtConf` to activate it".into()
      ),
      _ => (),
    } ;
    parse_success!(
      self for {
        stutter_arg!(self.write ;
          |w| {
            write!(w, "(set-option {} {})\n", option, value) ? ;
            Ok(())
          }
        )
      }
    )
  }
  /// Activates interactive mode.
  #[inline(always)]
  fn interactive_mode(& mut self) -> Res<()> {
    parse_success!(
      self for {
        stutter_arg!(self.write ;
          |w| write_str(w, "(set-option :interactive-mode true)\n")
        )
      }
    )
  }
  /// Activates print success.
  #[inline(always)]
  fn print_success(& mut self) -> Res<()> {
    parse_success!(
      self for {
        stutter_arg!(self.write ;
          |w| write_str(w, "(set-option :print-success true)\n")
        )
      }
    )
  }
  /// Activates unsat core production.
  #[inline(always)]
  fn produce_unsat_core(& mut self) -> Res<()> {
    parse_success!(
      self for {
        stutter_arg!(self.write ;
          |w| write_str(w, "(set-option :produce-unsat-cores true)\n")
        )
      }
    )
  }
  /// Shuts the solver down.
  #[inline(always)]
  fn exit(& mut self) -> Res<()> {
    parse_success!(
      self for {
        stutter_arg!(self.write ;
          |w| write_str(w, "(exit)\n")
        )
      }
    )
  }


  // |===| Modifying the assertion stack.

  /// Pushes `n` layers on the assertion stack.
  #[inline(always)]
  fn push(& mut self, n: u8) -> Res<()> {
    parse_success!(
      self for {
        stutter_arg!(self.write ;
          |w| {
            write!(w, "(push {})\n", n) ? ;
            Ok(())
          }
        )
      }
    )
  }
  /// Pops `n` layers off the assertion stack.
  #[inline(always)]
  fn pop(& mut self, n: u8) -> Res<()> {
    parse_success!(
      self for {
        stutter_arg!(self.write ;
          |w| {
            write!(w, "(pop {})\n", n) ? ;
            Ok(())
          }
        )
      }
    )
  }
  /// Resets the assertions in the solver.
  #[inline(always)]
  fn reset_assertions(& mut self) -> Res<()> {
    parse_success!(
      self for {
        stutter_arg!(self.write ;
          |w| write_str(w, "(reset-assertions)\n")
        )
      }
    )
  }


  // |===| Introducing new symbols.

  /// Declares a new sort.
  #[inline]
  fn declare_sort<Sort: Sort2Smt>(
    & mut self, sort: & Sort, arity: & u8
  ) -> Res<()> {
    parse_success!(
      self for {
        stutter_arg!(self.write ;
          |w| {
            write_str(w, "(declare-sort ") ? ;
            sort.sort_to_smt2(w) ? ;
            write!(w, " {})\n", arity) ? ;
            Ok(())
          }
        )
      }
    )
  }
  /// Defines a new sort.
  #[inline]
  fn define_sort<
    'a, Sort, I, Arg, ArgIter, Args: ?Sized, Body
  >(
    & mut self, sort: & Sort, args: & 'a Args, body: & Body, info: & I
  ) -> Res<()>
  where
  Sort: Sort2Smt,
  Arg: Expr2Smt<I> + 'a,
  Body: Expr2Smt<I>,
  ArgIter: Iterator<Item = & 'a Arg>,
  & 'a Args: IntoIterator<
    Item = & 'a Arg, IntoIter = ArgIter
  > {
    parse_success!(
      self for {
        stutter_arg!(self.write ;
          |w| {
            write_str(w, "( define-sort ") ? ;
            sort.sort_to_smt2(w) ? ;
            write_str(w, "\n   ( ") ? ;
            for arg in args {
              arg.expr_to_smt2(w, info) ? ;
              write_str(w, " ") ?
            }
            write_str(w, ")\n   ") ? ;
            body.expr_to_smt2(w, info) ? ;
            write_str(w, "\n)\n")
          }
        )
      }
    )
  }
  /// Declares a new function symbol.
  #[inline]
  fn declare_fun<
    'a, FunSym, ArgSort, ArgIter, Args: ?Sized, I, OutSort
  > (
    & mut self, symbol: & FunSym, args: & 'a Args, out: & OutSort, info: & I
  ) -> Res<()>
  where
  FunSym: Sym2Smt<I>,
  ArgSort: Sort2Smt + 'a,
  OutSort: Sort2Smt,
  ArgIter: Iterator<Item = & 'a ArgSort>,
  & 'a Args: IntoIterator<
    Item = & 'a ArgSort, IntoIter = ArgIter
  > {
    parse_success!(
      self for {
        stutter_arg!(self.write ;
          |w| {
            write_str(w, "(declare-fun ") ? ;
            symbol.sym_to_smt2(w, info) ? ;
            write_str(w, " ( ") ? ;
            for arg in args.into_iter() {
              arg.sort_to_smt2(w) ? ;
              write_str(w, " ") ?
            }
            write_str(w, ") ") ? ;
            out.sort_to_smt2(w) ? ;
            write_str(w, ")\n")
          }
        )
      }
    )
  }
  /// Declares a new constant.
  #[inline]
  fn declare_const<Sym: Sym2Smt<I>, Sort: Sort2Smt, I> (
    & mut self, symbol: & Sym, out_sort: & Sort, info: & I
  ) -> Res<()> {
    parse_success!(
      self for {
        stutter_arg!(self.write ;
          |w| {
            write_str(w, "(declare-const ") ? ;
            symbol.sym_to_smt2(w, info) ? ;
            write_str(w, " ") ? ;
            out_sort.sort_to_smt2(w) ? ;
            write_str(w, ")\n")
          }
        )
      }
    )
  }
  /// Defines a new function symbol.
  #[inline]
  fn define_fun<
    'a, FunSym, ArgSym, ArgSort, ArgIter, Args: ?Sized, OutSort, Body, I
  >(
    & mut self, symbol: & FunSym, args: & 'a Args,
    out: & OutSort, body: & Body, info: & I
  ) -> Res<()>
  where
  ArgSort: Sort2Smt + 'a,
  OutSort: Sort2Smt,
  FunSym: Sym2Smt<I>,
  ArgSym: Sym2Smt<I> + 'a,
  Body: Expr2Smt<I>,
  ArgIter: Iterator<Item = & 'a (ArgSym, ArgSort)>,
  & 'a Args: IntoIterator<
    Item = & 'a (ArgSym, ArgSort), IntoIter = ArgIter
  > {
    parse_success!(
      self for {
        stutter_arg!(self.write ;
          |w| {
            write_str(w, "(define-fun ") ? ;
            symbol.sym_to_smt2(w, info) ? ;
            write_str(w, " ( ") ? ;
            for arg in args {
              let (ref sym, ref sort) = * arg ;
              write_str(w, "(") ? ;
              sym.sym_to_smt2(w, info) ? ;
              write_str(w, " ") ? ;
              sort.sort_to_smt2(w) ? ;
              write_str(w, ") ") ?
            }
            write_str(w, ") ") ? ;
            out.sort_to_smt2(w) ? ;
            write_str(w, "\n   ") ? ;
            body.expr_to_smt2(w, info) ? ;
            write_str(w, "\n)\n")
          }
        )
      }
    )
  }
  /// Defines some new (possibily mutually) recursive functions.
  #[inline]
  fn define_funs_rec<
    'a, FunSym, ArgSym, ArgSort, ArgIter, Args, OutSort, Body,
    FunIter, Funs: ?Sized, I
  >(
    & mut self, funs: & 'a Funs, info: & I
  ) -> Res<()>
  where
  FunSym: Sym2Smt<I> + 'a,
  ArgSym: Sym2Smt<I> + 'a,
  ArgSort: Sort2Smt + 'a,
  OutSort: Sort2Smt + 'a,
  Body: Expr2Smt<I> + 'a,
  ArgIter: Iterator<Item = & 'a (ArgSym, ArgSort)>,
  & 'a Args: IntoIterator<
    Item = & 'a (ArgSym, ArgSort), IntoIter = ArgIter
  > + 'a,
  FunIter: Iterator<Item = & 'a (FunSym, Args, OutSort, Body)>,
  & 'a Funs: IntoIterator<
    Item = & 'a (FunSym, Args, OutSort, Body), IntoIter = FunIter
  > {
    parse_success!(
      self for {
        stutter_arg!(self.write ;
          |w| {
            // Header.
            write_str(w, "(define-funs-rec (\n") ? ;

            // Signatures.
            for fun in funs {
              let (ref sym, ref args, ref out, _) = * fun ;
              write_str(w, "   (") ? ;
              sym.sym_to_smt2(w, info) ? ;
              write_str(w, " ( ") ? ;
              for arg in args {
                let (ref sym, ref sort) = * arg ;
                write_str(w, "(") ? ;
                sym.sym_to_smt2(w, info) ? ;
                write_str(w, " ") ? ;
                sort.sort_to_smt2(w) ? ;
                write_str(w, ") ") ?
              }
              write_str(w, ") ") ? ;
              out.sort_to_smt2(w) ? ;
              write_str(w, ")\n") ?
            }
            write_str(w, " ) (") ? ;

            // Bodies
            for fun in funs {
              let (_, _, _, ref body) = * fun ;
              write_str(w, "\n   ") ? ;
              body.expr_to_smt2(w, info) ?
            }
            write_str(w, "\n )\n)\n")
          }
        )
      }
    )
  }
  /// Defines a new recursive function.
  #[inline]
  fn define_fun_rec<
    'a, FunSym, ArgSym, ArgSort, ArgIter, Args: ?Sized, OutSort, Body, I
  >(
    & mut self,  symbol: & FunSym, args: & 'a Args,
    out: & OutSort, body: & Body, info: & I
  ) -> Res<()>
  where
  ArgSort: Sort2Smt + 'a,
  OutSort: Sort2Smt,
  FunSym: Sym2Smt<I>,
  ArgSym: Sym2Smt<I> + 'a,
  Body: Expr2Smt<I>,
  ArgIter: Iterator<Item = & 'a (ArgSym, ArgSort)>,
  & 'a Args: IntoIterator<
    Item = & 'a (ArgSym, ArgSort), IntoIter = ArgIter
  > {
    parse_success!(
      self for {
        stutter_arg!(self.write ;
          |w| {
            // Header.
            write_str(w, "(define-fun-rec (\n") ? ;

            // Signature.
            write_str(w, "   (") ? ;
            symbol.sym_to_smt2(w, info) ? ;
            write_str(w, " ( ") ? ;
            for arg in args {
              let (ref sym, ref sort) = * arg ;
              write_str(w, "(") ? ;
              sym.sym_to_smt2(w, info) ? ;
              write_str(w, " ") ? ;
              sort.sort_to_smt2(w) ? ;
              write_str(w, ") ") ?
            }
            write_str(w, ") ") ? ;
            out.sort_to_smt2(w) ? ;
            write_str(w, ")\n") ? ;
            write_str(w, " ) (") ? ;

            // Body.
            write_str(w, "\n   ") ? ;
            body.expr_to_smt2(w, info) ? ;
            write_str(w, "\n )\n)\n")
          }
        )
      }
    )
  }


  // |===| Asserting and inspecting formulas.

  /// Asserts an expression with some print information.
  #[inline]
  fn assert<I, Expr: Expr2Smt<I>>(
    & mut self, expr: & Expr, info: & I
  ) -> Res<()> {
    parse_success!(
      self for {
        stutter_arg!(self.write ;
          |w| {
            write_str(w, "(assert\n  ") ? ;
            expr.expr_to_smt2(w, info) ? ;
            write_str(w, "\n)\n")
          }
        )
      }
    )
  }

  // |===| Inspecting settings.

  /// Get info command.
  #[inline(always)]
  fn get_info(& mut self, flag: & str) -> Res<()> {
    stutter_arg!(self.write ;
      |w| { write!(w, "(get-info {})\n", flag) ? ; Ok(()) }
    )
  }
  /// Get option command.
  #[inline(always)]
  fn get_option(& mut self, option: & str) -> Res<()> {
    stutter_arg!(self.write ;
      |w| { write!(w, "(get-option {})\n", option) ? ; Ok(()) }
    )
  }

  // |===| Script information.

  /// Set info command.
  #[inline(always)]
  fn set_info(& mut self, attribute: & str) -> Res<()> {
    stutter_arg!(self.write ;
      |w| { write!(w, "(set-info {})\n", attribute) ? ; Ok(()) }
    )
  }
  /// Echo command.
  #[inline(always)]
  fn echo(& mut self, text: & str) -> Res<()> {
    stutter_arg!(self.write ;
      |w| { write!(w, "(echo \"{}\")\n", text) ? ; Ok(()) }
    )
  }


  // |===| Parsing simple stuff.

  /// Parse success.
  #[inline]
  fn parse_success(& mut self) -> Res<()> {
    self.parse( |bytes, _| wrap!( success(bytes) ) )
  }

  /// Check-sat command.
  #[inline(always)]
  fn print_check_sat(& mut self) -> Res<()> {
    stutter_arg!(self.write ;
      |w| write_str(w, "(check-sat)\n")
    )
  }

  /// Parse the result of a check-sat, turns `unknown` results into errors.
  #[inline(always)]
  fn parse_check_sat(& mut self) -> Res<bool> {
    if let Some(res) = self.parse_check_sat_or_unknown() ? {
      Ok(res)
    } else {
      Err( ErrorKind::Unknown.into() )
    }
  }

  /// Parse the result of a check-sat, turns `unknown` results into `None`.
  #[inline(always)]
  fn parse_check_sat_or_unknown(& mut self) -> Res< Option<bool> > {
    self.parse( |bytes, _| wrap!( check_sat(bytes) ) )
  }

  /// Check-sat command, turns `unknown` results into errors.
  fn check_sat(& mut self) -> Res<bool> {
    self.print_check_sat() ? ;
    self.parse_check_sat()
  }

  /// Check-sat command, turns `unknown` results in `None`.
  fn check_sat_or_unknown(& mut self) -> Res< Option<bool> > {
    self.print_check_sat() ? ;
    self.parse_check_sat_or_unknown()
  }

  /// Get-model command.
  #[inline(always)]
  fn print_get_model(& mut self) -> Res<()> {
    stutter_arg!(self.write ;
      |w| write_str(w, "(get-model)\n")
    )
  }

  /// Parse the result of a get-model.
  fn parse_get_model<'a>(
    & 'a mut self
  ) -> Res<Vec<(Parser::Ident, Parser::Value)>>
  where Parser: 'a {
    self.parse(
      |bytes, parser| wrap!(
        alt!(
          bytes,
          unexpected |
          do_parse!(
            open_paren >>
            opt!(multispace) >>
            tag!("model") >>
            vec: many0!(
              do_parse!(
                open_paren >>
                opt!(multispace) >>
                tag!("define-fun") >>
                multispace >>
                id: call!(|bytes| parser.parse_ident(bytes)) >>
                open_paren >>
                close_paren >>
                opt!(multispace) >>
                alt_complete!(
                  tag!("Bool") | tag!("Int") | tag!("Real") |
                  tag!("bool") | tag!("int") | tag!("real")
                ) >>
                opt!(multispace) >>
                val: call!(|bytes| parser.parse_value(bytes)) >>
                close_paren >>
                ((id, val))
              )
            ) >>
            close_paren >>
            (Ok(vec))
          )
        )
      )
    )
  }

  /// Get-model command.
  fn get_model(& mut self) -> Res<Vec<(Parser::Ident, Parser::Value)>> {
    self.print_get_model() ? ;
    self.parse_get_model()
  }

  /// Parse the result of a get-values.
  fn parse_get_values(
    & mut self, info: & Parser::I
  ) -> Res<Vec<(Parser::Expr, Parser::Value)>> {
    self.parse(
      |bytes, parser| wrap!(
        alt_complete!(
          bytes,
          unexpected |
          do_parse!(
            open_paren >>
            vec: many0!(
              do_parse!(
                open_paren >>
                opt!(multispace) >>
                expr: call!(|bytes| parser.parse_expr(bytes, info)) >>
                multispace >>
                val: call!(|bytes| parser.parse_value(bytes)) >>
                close_paren >>
                ((expr, val))
              )
            ) >>
            close_paren >>
            (Ok(vec))
          )
        )
      )
    )
  }

  /// Get-assertions command.
  fn print_get_assertions(& mut self) -> Res<()> {
    stutter_arg!(self.write ;
      |w| write_str(w, "(get-assertions)\n")
    )
  }
  /// Get-assignment command.
  fn print_get_assignment(& mut self) -> Res<()> {
    stutter_arg!(self.write ;
      |w| write_str(w, "(get-assignment)\n")
    )
  }
  /// Get-unsat-assumptions command.
  fn print_get_unsat_assumptions(& mut self) -> Res<()> {
    stutter_arg!(self.write ;
      |w| write_str(w, "(get-unsat-assumptions)\n")
    )
  }
  /// Get-proop command.
  fn print_get_proof(& mut self) -> Res<()> {
    stutter_arg!(self.write ;
      |w| write_str(w, "(get-proof)\n")
    )
  }
  /// Get-unsat-core command.
  fn print_get_unsat_core(& mut self) -> Res<()> {
    stutter_arg!(self.write ;
      |w| write_str(w, "(get-unsat-core)\n")
    )
  }

  /// Get-values command.
  fn print_get_values<'a, Expr, ExprIter, Exprs: ?Sized>(
    & mut self, exprs: & 'a Exprs, info: & Parser::I
  ) -> Res<()>
  where
  Expr: Expr2Smt< Parser::I > + 'a,
  ExprIter: Iterator<Item = & 'a Expr>,
  & 'a Exprs: IntoIterator<
    Item = & 'a Expr, IntoIter = ExprIter
  > {
    stutter_arg!(self.write ;
      |w| {
        write!(w, "(get-value (") ? ;
        for e in exprs {
          write_str(w, "\n  ") ? ;
          e.expr_to_smt2(w, info) ?
        }
        write_str(w, "\n) )\n")
      }
    )
  }

  /// Get-values command.
  fn get_values<'a, Expr, ExprIter, Exprs: ?Sized>(
    & mut self, exprs: & 'a Exprs, info: & Parser::I
  ) -> Res<Vec<(Parser::Expr, Parser::Value)>>
  where
  Expr: Expr2Smt<Parser::I> +'a,
  ExprIter: Iterator<Item = & 'a Expr>,
  & 'a Exprs: IntoIterator<
    Item = & 'a Expr, IntoIter = ExprIter
  > {
    self.print_get_values(exprs, info) ? ;
    self.parse_get_values(info)
  }

  /// Check-sat with assumptions command.
  fn print_check_sat_assuming<'a, Ident, IdentIter, Idents: ?Sized>(
    & mut self, bool_vars: & 'a Idents, info: & Parser::I
  ) -> Res<()>
  where
  Ident: Sym2Smt<Parser::I> + 'a,
  IdentIter: Iterator<Item = & 'a Ident>,
  & 'a Idents: IntoIterator<
    Item = & 'a Ident, IntoIter = IdentIter
  > {
    match * self.solver().conf.get_check_sat_assuming() {
      Some(ref cmd) => {
        stutter_arg!(self.write ;
          |w| {
            write!(w, "({}\n ", cmd) ? ;
            for sym in bool_vars {
              write_str(w, " ") ? ;
              sym.sym_to_smt2(w, info) ?
            } ;
            write_str(w, "\n)\n")
          }
        )
      },
      _ => Err(
        format!(
          "check-sat-assuming is not supported for {}",
          self.solver().conf.style()
        ).into()
      ),
    }
  }

  /// Check-sat assuming command, turns `unknown` results into errors.
  fn check_sat_assuming<'a, Ident, IdentIter, Idents: ?Sized>(
    & mut self, idents: & 'a Idents, info: & Parser::I
  ) -> Res<bool>
  where
  Ident: Sym2Smt<Parser::I> + 'a,
  IdentIter: Iterator<Item = & 'a Ident>,
  & 'a Idents: IntoIterator<
    Item = & 'a Ident, IntoIter = IdentIter
  > {
    self.print_check_sat_assuming(idents, info) ? ;
    self.parse_check_sat()
  }

  /// Check-sat assuming command, turns `unknown` results into `None`.
  fn check_sat_assuming_or_unknown<'a, Ident, IdentIter, Idents: ?Sized>(
    & mut self, idents: & 'a Idents, info: & Parser::I
  ) -> Res<Option<bool>>
  where
  Ident: Sym2Smt<Parser::I> + 'a,
  IdentIter: Iterator<Item = & 'a Ident>,
  & 'a Idents: IntoIterator<
    Item = & 'a Ident, IntoIter = IdentIter
  > {
    self.print_check_sat_assuming(idents, info) ? ;
    self.parse_check_sat_or_unknown()
  }
}