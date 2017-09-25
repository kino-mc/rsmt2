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

use errors::* ;

use common::* ;
use conf::SolverConf ;
use parse::{ IdentParser, ValueParser, ExprParser } ;


/// Alias for the underlying parser.
pub type SmtParser<'kid> = ::parse::SmtParser<
  BufReader<& 'kid mut ChildStdout>
> ;


macro_rules! stutter_arg {
  ($slf:ident . $fun:ident ; $arg:expr) => (
    $slf.$fun($arg, $arg)
  ) ;
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
pub struct PlainSolver<'kid, Parser: Copy> {
  /// Solver configuration.
  conf: & 'kid SolverConf,
  /// Kid's stdin.
  stdin: BufWriter<& 'kid mut ChildStdin>,
  /// Stdout parser.
  smt_parser: SmtParser<'kid>,
  // /// Kid's stderr.
  // stderr: BufReader<& 'kid mut ChildStderr>,
  /// User-provided parser.
  parser: Parser,
}
impl<'kid, Parser: Copy> PlainSolver<'kid, Parser> {
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
      smt_parser: SmtParser::new(stdout),
      // stderr: stderr,
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
  'kid, Parser: Copy
> SolverBasic<'kid, Parser> for PlainSolver<'kid, Parser> {
  fn parsers(& mut self) -> (& mut SmtParser<'kid>, Parser) {
    (& mut self.smt_parser, self.parser)
  }
  // fn fetch(& mut self) -> Res<()> {
  //   fetch!(self)
  // }
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
  fn solver(& mut self) -> & mut PlainSolver<'kid, Parser> {
    self
  }
}

// impl<
//   'kid, Parser: ParseSmt2 + 'static
// > SolverPrims<'kid, Parser> for PlainSolver<'kid, Parser> {}

impl<
  'kid, Parser: Copy
> Solver<'kid, Parser> for PlainSolver<'kid, Parser> {}












/// Wrapper around a `PlainSolver` logging IOs to a file.
pub struct TeeSolver<'kid, Parser: Copy> {
  solver: PlainSolver<'kid, Parser>,
  file: BufWriter<File>,
}
impl<'kid, Parser: Copy> TeeSolver<'kid, Parser> {
  /// Configuration of the solver.
  pub fn conf(& self) -> & SolverConf { self.solver.conf }
}

impl<
  'kid, Parser: Copy
> SolverBasic<'kid, Parser> for TeeSolver<'kid, Parser> {
  fn parsers(& mut self) -> (& mut SmtParser<'kid>, Parser) {
    self.solver.parsers()
  }
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
  fn solver(& mut self) -> & mut PlainSolver<'kid, Parser> {
    & mut self.solver
  }
}

// impl<
//   'kid, Parser: ParseSmt2 + 'static
// > SolverPrims<'kid, Parser> for TeeSolver<'kid, Parser> {}

impl<
  'kid, Parser: Copy
> Solver<'kid, Parser> for TeeSolver<'kid, Parser> {}













/// Most basic function needed to provide SMT-LIB commands.
pub trait SolverBasic<'kid, Parser: Copy> {
  /// Accessor to the parser.
  #[inline]
  fn parsers(& mut self) -> (& mut SmtParser<'kid>, Parser) ;
  /// Applies a function to the writer on the solver's stdin.
  fn write<
    F: Fn(& mut BufWriter<& mut ChildStdin>) -> Res<()>,
    FTee: Fn(& mut BufWriter<File>) -> Res<()>,
  >(& mut self, f: F, f_tee: FTee) -> Res<()> ;
  /// Writes comments. Ignored for `PlainSolver`.
  fn comment(& mut self, txt: & str) -> Res<()> ;
  /// The plain solver.
  fn solver(& mut self) -> & mut PlainSolver<'kid, Parser> ;
}









/// Creates a solver from a kid.
pub fn solver<'kid, Parser: Copy>(
  kid: & 'kid mut Kid, parser: Parser
) -> Res< PlainSolver<'kid, Parser> > {
  PlainSolver::new(kid, parser)
}







/// Provides SMT-LIB commands.
pub trait Solver<
  'kid, Parser: Copy
> : SolverBasic<'kid, Parser> {


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
    'a, Sort, I, Arg, Args: ?Sized, Body
  >(
    & mut self, sort: & Sort, args: & 'a Args, body: & Body, info: & I
  ) -> Res<()>
  where
  Sort: Sort2Smt,
  Arg: Expr2Smt<I> + 'a,
  Body: Expr2Smt<I>,
  & 'a Args: IntoIterator< Item = & 'a Arg > {
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
    'a, FunSym, ArgSort, Args: ?Sized, I, OutSort
  > (
    & mut self, symbol: & FunSym, args: & 'a Args, out: & OutSort, info: & I
  ) -> Res<()>
  where
  FunSym: Sym2Smt<I>,
  ArgSort: Sort2Smt + 'a,
  OutSort: Sort2Smt,
  & 'a Args: IntoIterator< Item = & 'a ArgSort > {
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
    'a, FunSym, ArgSym, ArgSort, Args: ?Sized, OutSort, Body, I
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
  & 'a Args: IntoIterator< Item = & 'a (ArgSym, ArgSort) > {
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
    'a, FunSym, ArgSym, ArgSort, Args, OutSort, Body, Funs: ?Sized, I
  >(
    & mut self, funs: & 'a Funs, info: & I
  ) -> Res<()>
  where
  FunSym: Sym2Smt<I> + 'a,
  ArgSym: Sym2Smt<I> + 'a,
  ArgSort: Sort2Smt + 'a,
  OutSort: Sort2Smt + 'a,
  Body: Expr2Smt<I> + 'a,
  & 'a Args: IntoIterator< Item = & 'a (ArgSym, ArgSort) > + 'a,
  & 'a Funs: IntoIterator< Item = & 'a (FunSym, Args, OutSort, Body) > {
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
    'a, FunSym, ArgSym, ArgSort, Args: ?Sized, OutSort, Body, I
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
  & 'a Args: IntoIterator< Item = & 'a (ArgSym, ArgSort) > {
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


  /// Check-sat command.
  #[inline(always)]
  fn print_check_sat(& mut self) -> Res<()> {
    stutter_arg!(self.write ;
      |w| write_str(w, "(check-sat)\n")
    )
  }

  /// Get-model command.
  #[inline(always)]
  fn print_get_model(& mut self) -> Res<()> {
    stutter_arg!(self.write ;
      |w| write_str(w, "(get-model)\n")
    )
  }

  /// Parse the result of a get-model.
  fn parse_get_model<Ident, Type, Value>(
    & mut self
  ) -> Res<Vec<(Ident, Vec<Type>, Type, Value)>>
  where
  Parser: for<'a> IdentParser<'a, Ident, Type, & 'a mut SmtParser<'kid>> +
          for<'a> ValueParser<'a, Value, & 'a mut SmtParser<'kid>> {
    let (smt_parser, parser) = self.parsers() ;
    smt_parser.get_model(parser)
  }

  /// Get-model command.
  fn get_model<Ident, Type, Value>(
    & mut self
  ) -> Res<Vec<(Ident, Vec<Type>, Type, Value)>>
  where
  Parser: for<'a> IdentParser<'a, Ident, Type, & 'a mut SmtParser<'kid>> +
          for<'a> ValueParser<'a, Value, & 'a mut SmtParser<'kid>> {
    self.print_get_model() ? ;
    self.parse_get_model()
  }

  /// Parse the result of a get-model where all the symbols are nullary.
  fn parse_get_model_const<Ident, Type, Value>(
    & mut self
  ) -> Res<Vec<(Ident, Type, Value)>>
  where
  Parser: for<'a> IdentParser<'a, Ident, Type, & 'a mut SmtParser<'kid>> +
          for<'a> ValueParser<'a, Value, & 'a mut SmtParser<'kid>> {
    let (smt_parser, parser) = self.parsers() ;
    smt_parser.get_model_const(parser)
  }

  /// Get-model command when all the symbols are nullary.
  fn get_model_const<Ident, Type, Value>(
    & mut self
  ) -> Res<Vec<(Ident, Type, Value)>>
  where
  Parser: for<'a> IdentParser<'a, Ident, Type, & 'a mut SmtParser<'kid>> +
          for<'a> ValueParser<'a, Value, & 'a mut SmtParser<'kid>> {
    self.print_get_model() ? ;
    self.parse_get_model_const()
  }



  /// Parse success.
  #[inline]
  fn parse_success(& mut self) -> Res<()> {
    self.parsers().0.success()
  }

  /// Parse the result of a check-sat, turns `unknown` results into errors.
  #[inline(always)]
  fn parse_check_sat(& mut self) -> Res<bool> {
    if let Some(res) = self.parsers().0.check_sat() ? {
      Ok(res)
    } else {
      Err( ErrorKind::Unknown.into() )
    }
  }

  /// Parse the result of a check-sat, turns `unknown` results into `None`.
  #[inline(always)]
  fn parse_check_sat_or_unknown(& mut self) -> Res< Option<bool> > {
    self.parsers().0.check_sat()
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
  /// Get-proof command.
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
  fn print_get_values<'a, Info, Expr, Exprs: ?Sized>(
    & mut self, exprs: & 'a Exprs, info: & Info
  ) -> Res<()>
  where
  Expr: Expr2Smt< Info > + 'a,
  & 'a Exprs: IntoIterator< Item = & 'a Expr > {
    stutter_arg!(self.write ;
      |w| {
        write!(w, "(get-value (") ? ;
        for e in exprs {
          write_str(w, "\n  ") ? ;
          e.expr_to_smt2(w, & info) ?
        }
        write_str(w, "\n) )\n")
      }
    )
  }

  /// Parse the result of a get-values.
  fn parse_get_values<Info: Clone, Expr, Value>(
    & mut self, info: Info
  ) -> Res<Vec<(Expr, Value)>>
  where
  Parser: for<'a> ExprParser<'a, Expr, Info, & 'a mut SmtParser<'kid>> +
          for<'a> ValueParser<'a, Value, & 'a mut SmtParser<'kid>> {
    let (smt_parser, parser) = self.parsers() ;
    smt_parser.get_values(parser, info)
  }

  /// Get-values command.
  fn get_values<
    'a, Info: Clone, Expr, Exprs: ?Sized, Value
  >(
    & mut self, exprs: & 'a Exprs, info: Info
  ) -> Res<Vec<(Expr, Value)>>
  where
  Parser: for<'b> ExprParser<'b, Expr, Info, & 'b mut SmtParser<'kid>> +
          for<'b> ValueParser<'b, Value, & 'b mut SmtParser<'kid>>,
  Expr: Expr2Smt<Info> + 'a,
  & 'a Exprs: IntoIterator< Item = & 'a Expr > {
    self.print_get_values(exprs, & info) ? ;
    self.parse_get_values(info)
  }

  /// Check-sat with assumptions command.
  fn print_check_sat_assuming<'a, Info, Ident, Idents: ?Sized>(
    & mut self, bool_vars: & 'a Idents, info: & Info
  ) -> Res<()>
  where
  Ident: Sym2Smt<Info> + 'a,
  & 'a Idents: IntoIterator< Item = & 'a Ident > {
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
  fn check_sat_assuming<'a, Info, Ident, Idents: ?Sized>(
    & mut self, idents: & 'a Idents, info: & Info
  ) -> Res<bool>
  where
  Ident: Sym2Smt<Info> + 'a,
  & 'a Idents: IntoIterator< Item = & 'a Ident > {
    self.print_check_sat_assuming(idents, info) ? ;
    self.parse_check_sat()
  }

  /// Check-sat assuming command, turns `unknown` results into `None`.
  fn check_sat_assuming_or_unknown<'a, Info, Ident, Idents: ?Sized>(
    & mut self, idents: & 'a Idents, info: & Info
  ) -> Res<Option<bool>>
  where
  Ident: Sym2Smt<Info> + 'a,
  & 'a Idents: IntoIterator< Item = & 'a Ident > {
    self.print_check_sat_assuming(idents, info) ? ;
    self.parse_check_sat_or_unknown()
  }
}