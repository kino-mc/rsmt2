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





/// Prefix of an actlit identifier.
#[allow(non_upper_case_globals)]
pub static actlit_pref: & str = "|rsmt2 actlit " ;
/// Suffix of an actlit identifier.
#[allow(non_upper_case_globals)]
pub static actlit_suff: & str = "|" ;

/// An activation literal is an opaque wrapper around a `usize`.
///
/// Obtained by a solver's [`get_actlit`][get actlit].
///
/// [get actlit]: ../trait.Solver.html#method.get_actlit (get_actlit documentation)
pub struct Actlit {
  /// ID of the actlit.
  id: usize,
}
impl Actlit {
  /// Unique number of this actlit.
  pub fn uid(& self) -> usize { self.id }
  /// Writes the actlit as an SMT-LIB 2 symbol.
  pub fn write<W>(& self, w: & mut W) -> SmtRes<()> where W: Write {
    write!(w, "{}{}{}", actlit_pref, self.id, actlit_suff) ? ;
    Ok(())
  }
}
impl ::std::ops::Deref for Actlit {
  type Target = usize ;
  fn deref(& self) -> & usize {
    & self.id
  }
}





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
  pub fn new(conf: SolverConf) -> SmtRes<Self> {
    let cmd = conf.get_cmd().to_string() ;
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
      || format!("while spawning child process with {}", cmd).into()
    )
  }
  /// Creates a solver kid with the default configuration. Mostly used in
  /// tests.
  pub fn default() -> SmtRes<Self> {
    Self::new( SolverConf::z3() )
  }

  /// Kills the solver kid.
  ///
  /// The windows version just prints `(exit)\n` on the kid's `stdin`. Anything
  /// else seems to cause problems.
  #[cfg(windows)]
  pub fn kill(mut self) -> SmtRes<()> {
    if let Some(stdin) = self.kid.stdin.as_mut() {
      let _ = writeln!(stdin, "(exit)\n") ;
    }
    Ok(())
  }
  #[cfg(not(windows))]
  pub fn kill(mut self) -> SmtRes<()> {
    if let Some(stdin) = self.kid.stdin.as_mut() {
      let _ = writeln!(stdin, "(exit)\n") ;
    }
    if let None = self.kid.try_wait().chain_err(
      || "waiting for child process to exit"
    ) ? {
      self.kid.kill().chain_err::<_, ErrorKind>(
        || "while killing child process".into()
      ) ?
    }
    Ok(())
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
  /// User-provided parser.
  parser: Parser,
  /// Actlit counter.
  actlit: usize,
}
impl<'kid, Parser: Copy> PlainSolver<'kid, Parser> {
  /// Creates a plain solver.
  pub fn new(kid: & 'kid mut Kid, parser: Parser) -> SmtRes<Self> {
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
      actlit: 0,
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
  fn next_actlit(& mut self) -> usize {
    let res = self.actlit ;
    self.actlit += 1 ;
    res
  }
  fn has_actlits(& self) -> bool { self.actlit != 0 }
  fn reset_actlits(& mut self) { self.actlit = 0 }
  fn parsers(& mut self) -> SmtRes<(& mut SmtParser<'kid>, Parser)> {
    let smt_parser = & mut self.smt_parser ;
    smt_parser.try_error() ? ;
    Ok( (smt_parser, self.parser) )
  }
  // fn fetch(& mut self) -> SmtRes<()> {
  //   fetch!(self)
  // }
  fn write<
    F: Fn(& mut BufWriter<& mut ChildStdin>) -> SmtRes<()>,
    FTee: Fn(& mut BufWriter<File>) -> SmtRes<()>,
  >(& mut self, f: F, _: FTee) -> SmtRes<()> {
    try!( f(& mut self.stdin) ) ;
    self.stdin.flush() ? ;
    Ok(())
  }
  fn comment(& mut self, _: & str) -> SmtRes<()> {
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
  fn next_actlit(& mut self) -> usize {
    self.solver.next_actlit()
  }
  fn has_actlits(& self) -> bool { self.solver.has_actlits() }
  fn reset_actlits(& mut self) { self.solver.reset_actlits() }
  fn parsers(& mut self) -> SmtRes<(& mut SmtParser<'kid>, Parser)> {
    self.solver.parsers()
  }
  fn write<
    F: Fn(& mut BufWriter<& mut ChildStdin>) -> SmtRes<()>,
    FTee: Fn(& mut BufWriter<File>) -> SmtRes<()>,
  >(& mut self, f: F, f_tee: FTee) -> SmtRes<()> {
    f(& mut self.solver.stdin) ? ;
    self.solver.stdin.flush() ? ;
    // write_str(& mut self.file, "\n") ? ;
    f_tee(& mut self.file) ? ;
    self.file.flush() ? ;
    Ok(())
  }
  fn comment(& mut self, txt: & str) -> SmtRes<()> {
    for line in txt.lines() {
      write!(self.file, "\n;; {}", line) ?
    }
    write!(self.file, "\n") ? ;
    self.file.flush() ? ;
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
  /// ID of the next activation literal.
  #[inline]
  fn next_actlit(& mut self) -> usize ;
  /// True if at least one actlit was requested in the past.
  #[inline]
  fn has_actlits(& self) -> bool ;
  /// Cancels all previous calls to `next_actlit`.
  #[inline]
  fn reset_actlits(& mut self) ;
  /// Accessor to the parser.
  #[inline]
  fn parsers(& mut self) -> SmtRes<(& mut SmtParser<'kid>, Parser)> ;
  /// Applies a function to the writer on the solver's stdin.
  fn write<
    F: Fn(& mut BufWriter<& mut ChildStdin>) -> SmtRes<()>,
    FTee: Fn(& mut BufWriter<File>) -> SmtRes<()>,
  >(& mut self, f: F, f_tee: FTee) -> SmtRes<()> ;
  /// Writes comments. Ignored for `PlainSolver`.
  fn comment(& mut self, txt: & str) -> SmtRes<()> ;
  /// The plain solver.
  fn solver(& mut self) -> & mut PlainSolver<'kid, Parser> ;
}









/// Creates a solver from a kid.
pub fn solver<'kid, Parser: Copy>(
  kid: & 'kid mut Kid, parser: Parser
) -> SmtRes< PlainSolver<'kid, Parser> > {
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
  ) -> SmtRes<()> {
    parse_success!(
      self for {
        stutter_arg!(
          self.write ; |w| write_str(w, "(reset)\n")
        )
      }
    ) ? ;
    self.reset_actlits() ;
    Ok(())
  }



  /// Sets the logic.
  #[inline]
  fn set_logic(
    & mut self, logic: Logic
  ) -> SmtRes<()> {
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
  ) -> SmtRes<()> {
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
  fn interactive_mode(& mut self) -> SmtRes<()> {
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
  fn print_success(& mut self) -> SmtRes<()> {
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
  fn produce_unsat_core(& mut self) -> SmtRes<()> {
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
  fn exit(& mut self) -> SmtRes<()> {
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
  fn push(& mut self, n: u8) -> SmtRes<()> {
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
  fn pop(& mut self, n: u8) -> SmtRes<()> {
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
  fn reset_assertions(& mut self) -> SmtRes<()> {
    parse_success!(
      self for {
        stutter_arg!(self.write ;
          |w| write_str(w, "(reset-assertions)\n")
        )
      }
    )
  }


  // |===| Introducing new symbols.

  /// Introduces a new actlit.
  #[inline]
  fn get_actlit(& mut self) -> SmtRes<Actlit> {
    let next_actlit = Actlit { id: self.next_actlit() } ;
    parse_success!(
      self for {
        stutter_arg!(self.write ;
          |w| {
            write!(
              w, "(declare-fun {}{}{} () Bool)",
              actlit_pref, next_actlit.id, actlit_suff
            ) ? ;
            Ok(())
          }
        )
      }
    ) ? ;
    Ok(next_actlit)
  }

  /// Deactivates an activation literal, alias for
  /// `solver.set_actlit(actlit, false)`.
  #[inline]
  fn de_actlit(& mut self, actlit: Actlit) -> SmtRes<()> {
    self.set_actlit(actlit, false)
  }

  /// Forces the value of an actlit and consumes it.
  #[inline]
  fn set_actlit(
    & mut self, actlit: Actlit, b: bool
  ) -> SmtRes<()> {
    parse_success!(
      self for {
        stutter_arg!(self.write ;
          |w| {
            if b {
              write!(w, "(assert ") ?
            } else {
              write!(w, "(assert (not ") ?
            }
            actlit.write(w) ? ;
            if b {
              write!(w, ")\n") ?
            } else {
              write!(w, ") )\n") ?
            }
            Ok(())
          }
        )
      }
    )
  }

  /// Declares a new sort.
  #[inline]
  fn declare_sort<Sort: Sort2Smt>(
    & mut self, sort: & Sort, arity: & u8
  ) -> SmtRes<()> {
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
  fn define_sort<'a, Sort, Arg, Args, Body>(
    & mut self, sort: & Sort, args: Args, body: & Body
  ) -> SmtRes<()>
  where
  Sort: Sort2Smt,
  Arg: Expr2Smt<()> + 'a,
  Body: Expr2Smt<()>,
  Args: Copy + IntoIterator< Item = & 'a Arg > {
    self.define_sort_with(sort, args, body, ())
  }

  /// Defines a new sort.
  #[inline]
  fn define_sort_with<'a, Sort, Info, Arg, Args, Body>(
    & mut self, sort: & Sort, args: Args, body: & Body, info: Info
  ) -> SmtRes<()>
  where
  Info: Copy,
  Sort: Sort2Smt,
  Arg: Expr2Smt<Info> + 'a,
  Body: Expr2Smt<Info>,
  Args: Copy + IntoIterator< Item = & 'a Arg > {
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
  fn declare_fun<'a, FunSym, ArgSort, Args, OutSort> (
    & mut self, symbol: & FunSym, args: Args, out: & OutSort
  ) -> SmtRes<()>
  where
  FunSym: ?Sized + Sym2Smt<()>,
  ArgSort: ?Sized + Sort2Smt + 'a,
  OutSort: ?Sized + Sort2Smt,
  Args: Copy + IntoIterator< Item = & 'a ArgSort > {
    self.declare_fun_with(symbol, args, out, ())
  }

  /// Declares a new function symbol.
  #[inline]
  fn declare_fun_with<'a, Info, FunSym, ArgSort, Args, OutSort> (
    & mut self, symbol: & FunSym, args: Args, out: & OutSort, info: Info
  ) -> SmtRes<()>
  where
  Info: Copy,
  FunSym: ?Sized + Sym2Smt<Info>,
  ArgSort: ?Sized + Sort2Smt + 'a,
  OutSort: ?Sized + Sort2Smt,
  Args: Copy + IntoIterator< Item = & 'a ArgSort > {
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
  fn declare_const<Sym, Sort> (
    & mut self, symbol: & Sym, out_sort: & Sort
  ) -> SmtRes<()>
  where Sym: ?Sized + Sym2Smt<()>, Sort: ?Sized + Sort2Smt {
    self.declare_const_with(symbol, out_sort, ())
  }

  /// Declares a new constant.
  #[inline]
  fn declare_const_with<Info, Sym, Sort> (
    & mut self, symbol: & Sym, out_sort: & Sort, info: Info
  ) -> SmtRes<()>
  where Info: Copy, Sym: ?Sized + Sym2Smt<Info>, Sort: ?Sized + Sort2Smt {
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
    'a, FunSym, ArgSym, ArgSort, Args, OutSort, Body
  >(
    & mut self, symbol: & FunSym, args: Args, out: & OutSort, body: & Body
  ) -> SmtRes<()>
  where
  ArgSort: Sort2Smt + 'a,
  OutSort: Sort2Smt,
  FunSym: Sym2Smt<()>,
  ArgSym: Sym2Smt<()> + 'a,
  Body: Expr2Smt<()>,
  Args: Copy + IntoIterator< Item = & 'a (ArgSym, ArgSort) > {
    self.define_fun_with(symbol, args, out, body, ())
  }

  /// Defines a new function symbol.
  #[inline]
  fn define_fun_with<
    'a, Info, FunSym, ArgSym, ArgSort, Args, OutSort, Body
  >(
    & mut self, symbol: & FunSym, args: Args,
    out: & OutSort, body: & Body, info: Info
  ) -> SmtRes<()>
  where
  Info: Copy,
  ArgSort: Sort2Smt + 'a,
  OutSort: Sort2Smt,
  FunSym: Sym2Smt<Info>,
  ArgSym: Sym2Smt<Info> + 'a,
  Body: Expr2Smt<Info>,
  Args: Copy + IntoIterator< Item = & 'a (ArgSym, ArgSort) > {
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
    'a, FunSym, ArgSym, ArgSort, Args, OutSort, Body, Funs
  >(
    & mut self, funs: Funs
  ) -> SmtRes<()>
  where
  FunSym: Sym2Smt<()> + 'a,
  ArgSym: Sym2Smt<()> + 'a,
  ArgSort: Sort2Smt + 'a,
  OutSort: Sort2Smt + 'a,
  Body: Expr2Smt<()> + 'a,
  & 'a Args: IntoIterator< Item = & 'a (ArgSym, ArgSort) > + 'a,
  Funs: Copy + IntoIterator< Item = & 'a (FunSym, Args, OutSort, Body) > {
    self.define_funs_rec_with(funs, ())
  }

  /// Defines some new (possibily mutually) recursive functions.
  #[inline]
  fn define_funs_rec_with<
    'a, Info, FunSym, ArgSym, ArgSort, Args, OutSort, Body, Funs
  >(
    & mut self, funs: Funs, info: Info
  ) -> SmtRes<()>
  where
  Info: Copy,
  FunSym: Sym2Smt<Info> + 'a,
  ArgSym: Sym2Smt<Info> + 'a,
  ArgSort: Sort2Smt + 'a,
  OutSort: Sort2Smt + 'a,
  Body: Expr2Smt<Info> + 'a,
  & 'a Args: IntoIterator< Item = & 'a (ArgSym, ArgSort) > + 'a,
  Funs: Copy + IntoIterator< Item = & 'a (FunSym, Args, OutSort, Body) > {
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
    'a, FunSym, ArgSym, ArgSort, Args, OutSort, Body
  >(
    & mut self,  symbol: & FunSym, args: Args, out: & OutSort, body: & Body
  ) -> SmtRes<()>
  where
  ArgSort: Sort2Smt + 'a,
  OutSort: Sort2Smt,
  FunSym: Sym2Smt<()>,
  ArgSym: Sym2Smt<()> + 'a,
  Body: Expr2Smt<()>,
  Args: Copy + IntoIterator< Item = & 'a (ArgSym, ArgSort) > {
    self.define_fun_rec_with(symbol, args, out, body, ())
  }

  /// Defines a new recursive function.
  #[inline]
  fn define_fun_rec_with<
    'a, Info, FunSym, ArgSym, ArgSort, Args, OutSort, Body
  >(
    & mut self,  symbol: & FunSym, args: Args,
    out: & OutSort, body: & Body, info: Info
  ) -> SmtRes<()>
  where
  Info: Copy,
  ArgSort: Sort2Smt + 'a,
  OutSort: Sort2Smt,
  FunSym: Sym2Smt<Info>,
  ArgSym: Sym2Smt<Info> + 'a,
  Body: Expr2Smt<Info>,
  Args: Copy + IntoIterator< Item = & 'a (ArgSym, ArgSort) > {
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

  /// Asserts an expression without print information.
  #[inline]
  fn assert<Expr>(
    & mut self, expr: & Expr
  ) -> SmtRes<()>
  where Expr: ?Sized + Expr2Smt<()> {
    self.assert_with(expr, ())
  }

  /// Asserts an expression without print information, guarded by an activation
  /// literal.
  #[inline]
  fn assert_act<Expr>(
    & mut self, actlit: & Actlit, expr: & Expr
  ) -> SmtRes<()>
  where Expr: ?Sized + Expr2Smt<()> {
    self.assert_act_with(actlit, expr, ())
  }

  /// Asserts an expression with some print information.
  #[inline]
  fn assert_with<Info, Expr>(
    & mut self, expr: & Expr, info: Info
  ) -> SmtRes<()>
  where
  Info: Copy,
  Expr: ?Sized + Expr2Smt<Info> {
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

  /// Asserts an expression with some print information, guarded by an
  /// activation literal.
  #[inline]
  fn assert_act_with<Info, Expr>(
    & mut self, actlit: & Actlit, expr: & Expr, info: Info
  ) -> SmtRes<()>
  where
  Info: Copy,
  Expr: ?Sized + Expr2Smt<Info>, {
    parse_success!(
      self for {
        stutter_arg!(self.write ;
          |w| {
            write_str(w, "(assert\n  (=>\n    ") ? ;
            actlit.write(w) ? ;
            write_str(w, "\n    ") ? ;
            expr.expr_to_smt2(w, info) ? ;
            write_str(w, "\n  )\n)\n")
          }
        )
      }
    )
  }

  // |===| Inspecting settings.

  /// Get info command.
  #[inline(always)]
  fn get_info(& mut self, flag: & str) -> SmtRes<()> {
    stutter_arg!(self.write ;
      |w| { write!(w, "(get-info {})\n", flag) ? ; Ok(()) }
    )
  }
  /// Get option command.
  #[inline(always)]
  fn get_option(& mut self, option: & str) -> SmtRes<()> {
    stutter_arg!(self.write ;
      |w| { write!(w, "(get-option {})\n", option) ? ; Ok(()) }
    )
  }

  // |===| Script information.

  /// Set info command.
  #[inline(always)]
  fn set_info(& mut self, attribute: & str) -> SmtRes<()> {
    stutter_arg!(self.write ;
      |w| { write!(w, "(set-info {})\n", attribute) ? ; Ok(()) }
    )
  }
  /// Echo command.
  #[inline(always)]
  fn echo(& mut self, text: & str) -> SmtRes<()> {
    stutter_arg!(self.write ;
      |w| { write!(w, "(echo \"{}\")\n", text) ? ; Ok(()) }
    )
  }


  /// Check-sat command.
  #[inline(always)]
  fn print_check_sat(& mut self) -> SmtRes<()> {
    stutter_arg!(self.write ;
      |w| write_str(w, "(check-sat)\n")
    )
  }
  /// Check-sat command, with actlits.
  #[inline(always)]
  fn print_check_sat_act<'a, Actlits>(
    & mut self, actlits: Actlits
  ) -> SmtRes<()>
  where
  Actlits: Copy + IntoIterator<Item = & 'a Actlit> {
    stutter_arg!(self.write ;
      |w| {
        write_str(w, "(check-sat") ? ;
        for actlit in actlits {
          write!(w, " ") ? ;
          actlit.write(w) ?
        }
        write_str(w, ")\n")
      }
    )
  }

  /// Get-model command.
  #[inline(always)]
  fn print_get_model(& mut self) -> SmtRes<()> {
    stutter_arg!(self.write ;
      |w| write_str(w, "(get-model)\n")
    )
  }

  /// Parse the result of a get-model.
  fn parse_get_model<Ident, Type, Value>(
    & mut self
  ) -> SmtRes<Vec<(Ident, Vec<Type>, Type, Value)>>
  where
  Parser: for<'a> IdentParser<Ident, Type, & 'a mut SmtParser<'kid>> +
          for<'a> ValueParser<Value, & 'a mut SmtParser<'kid>> {
    let has_actlits = self.has_actlits() ;
    let (smt_parser, parser) = self.parsers()? ;
    smt_parser.get_model(has_actlits, parser)
  }

  /// Get-model command.
  fn get_model<Ident, Type, Value>(
    & mut self
  ) -> SmtRes<Vec<(Ident, Vec<Type>, Type, Value)>>
  where
  Parser: for<'a> IdentParser<Ident, Type, & 'a mut SmtParser<'kid>> +
          for<'a> ValueParser<Value, & 'a mut SmtParser<'kid>> {
    self.print_get_model() ? ;
    self.parse_get_model()
  }

  /// Parse the result of a get-model where all the symbols are nullary.
  fn parse_get_model_const<Ident, Type, Value>(
    & mut self
  ) -> SmtRes<Vec<(Ident, Type, Value)>>
  where
  Parser: for<'a> IdentParser<Ident, Type, & 'a mut SmtParser<'kid>> +
          for<'a> ValueParser<Value, & 'a mut SmtParser<'kid>> {
    let has_actlits = self.has_actlits() ;
    let (smt_parser, parser) = self.parsers()? ;
    smt_parser.get_model_const(has_actlits, parser)
  }

  /// Get-model command when all the symbols are nullary.
  fn get_model_const<Ident, Type, Value>(
    & mut self
  ) -> SmtRes<Vec<(Ident, Type, Value)>>
  where
  Parser: for<'a> IdentParser<Ident, Type, & 'a mut SmtParser<'kid>> +
          for<'a> ValueParser<Value, & 'a mut SmtParser<'kid>> {
    self.print_get_model() ? ;
    self.parse_get_model_const()
  }



  /// Parse success.
  #[inline]
  fn parse_success(& mut self) -> SmtRes<()> {
    self.parsers()?.0.success()
  }

  /// Parse the result of a check-sat, turns `unknown` results into errors.
  #[inline(always)]
  fn parse_check_sat(& mut self) -> SmtRes<bool> {
    if let Some(res) = self.parsers()?.0.check_sat() ? {
      Ok(res)
    } else {
      Err( ErrorKind::Unknown.into() )
    }
  }

  /// Parse the result of a check-sat, turns `unknown` results into `None`.
  #[inline(always)]
  fn parse_check_sat_or_unknown(& mut self) -> SmtRes< Option<bool> > {
    self.parsers()?.0.check_sat()
  }

  /// Check-sat command, turns `unknown` results into errors.
  fn check_sat(& mut self) -> SmtRes<bool> {
    self.print_check_sat() ? ;
    self.parse_check_sat()
  }
  /// Check-sat command with activation literals, turns `unknown` results into
  /// errors.
  fn check_sat_act<'a, Actlits>(
    & mut self, actlits: Actlits
  ) -> SmtRes<bool>
  where
  Actlits: Copy + IntoIterator<Item = & 'a Actlit> {
    self.print_check_sat_act(actlits) ? ;
    self.parse_check_sat()
  }

  /// Check-sat command, turns `unknown` results in `None`.
  fn check_sat_or_unknown(& mut self) -> SmtRes< Option<bool> > {
    self.print_check_sat() ? ;
    self.parse_check_sat_or_unknown()
  }
  /// Check-sat command with activation literals, turns `unknown` results in
  /// `None`.
  fn check_sat_act_or_unknown<'a, Actlits>(
    & mut self, actlits: Actlits
  ) -> SmtRes< Option<bool> >
  where
  Actlits: Copy + IntoIterator<Item = & 'a Actlit> {
    self.print_check_sat_act(actlits) ? ;
    self.parse_check_sat_or_unknown()
  }

  /// Get-assertions command.
  fn print_get_assertions(& mut self) -> SmtRes<()> {
    stutter_arg!(self.write ;
      |w| write_str(w, "(get-assertions)\n")
    )
  }
  /// Get-assignment command.
  fn print_get_assignment(& mut self) -> SmtRes<()> {
    stutter_arg!(self.write ;
      |w| write_str(w, "(get-assignment)\n")
    )
  }
  /// Get-unsat-assumptions command.
  fn print_get_unsat_assumptions(& mut self) -> SmtRes<()> {
    stutter_arg!(self.write ;
      |w| write_str(w, "(get-unsat-assumptions)\n")
    )
  }
  /// Get-proof command.
  fn print_get_proof(& mut self) -> SmtRes<()> {
    stutter_arg!(self.write ;
      |w| write_str(w, "(get-proof)\n")
    )
  }
  /// Get-unsat-core command.
  fn print_get_unsat_core(& mut self) -> SmtRes<()> {
    stutter_arg!(self.write ;
      |w| write_str(w, "(get-unsat-core)\n")
    )
  }

  /// Get-values command.
  fn print_get_values<'a, Expr, Exprs>(
    & mut self, exprs: Exprs
  ) -> SmtRes<()>
  where
  Expr: ?Sized + Expr2Smt<()> + 'a,
  Exprs: Clone + IntoIterator< Item = & 'a Expr > {
    self.print_get_values_with(exprs, ())
  }

  /// Get-values command.
  fn print_get_values_with<'a, Info, Expr, Exprs>(
    & mut self, exprs: Exprs, info: Info
  ) -> SmtRes<()>
  where
  Info: Copy,
  Expr: ?Sized + Expr2Smt< Info > + 'a,
  Exprs: Clone + IntoIterator< Item = & 'a Expr > {
    stutter_arg!(self.write ;
      |w| {
        write!(w, "(get-value (") ? ;
        for e in exprs.clone() {
          write_str(w, "\n  ") ? ;
          e.expr_to_smt2(w, info) ?
        }
        write_str(w, "\n) )\n")
      }
    )
  }

  /// Parse the result of a get-values.
  fn parse_get_values<Expr, Value>(
    & mut self
  ) -> SmtRes<Vec<(Expr, Value)>>
  where
  Parser: for<'a> ExprParser<Expr, (), & 'a mut SmtParser<'kid>> +
          for<'a> ValueParser<Value, & 'a mut SmtParser<'kid>> {
    self.parse_get_values_with(())
  }

  /// Parse the result of a get-values.
  fn parse_get_values_with<Info, Expr, Value>(
    & mut self, info: Info
  ) -> SmtRes<Vec<(Expr, Value)>>
  where
  Info: Copy,
  Parser: for<'a> ExprParser<Expr, Info, & 'a mut SmtParser<'kid>> +
          for<'a> ValueParser<Value, & 'a mut SmtParser<'kid>> {
    let (smt_parser, parser) = self.parsers()? ;
    smt_parser.get_values(parser, info)
  }

  /// Get-values command.
  ///
  /// Notice that the input expression type and the output one have no reason
  /// to be the same.
  fn get_values<'a, Expr, Exprs, PExpr, PValue>(
    & mut self, exprs: Exprs
  ) -> SmtRes<Vec<(PExpr, PValue)>>
  where
  Parser: for<'b> ExprParser<PExpr, (), & 'b mut SmtParser<'kid>> +
          for<'b> ValueParser<PValue, & 'b mut SmtParser<'kid>>,
  Expr: ?Sized + Expr2Smt<()> + 'a,
  Exprs: Copy + IntoIterator< Item = & 'a Expr > {
    self.get_values_with(exprs, ())
  }

  /// Get-values command.
  ///
  /// Notice that the input expression type and the output one have no reason
  /// to be the same.
  fn get_values_with<
    'a, Info, Expr, Exprs, PExpr, PValue
  >(
    & mut self, exprs: Exprs, info: Info
  ) -> SmtRes<Vec<(PExpr, PValue)>>
  where
  Info: Copy,
  Parser: for<'b> ExprParser<PExpr, Info, & 'b mut SmtParser<'kid>> +
          for<'b> ValueParser<PValue, & 'b mut SmtParser<'kid>>,
  Expr: ?Sized + Expr2Smt<Info> + 'a,
  Exprs: Copy + IntoIterator< Item = & 'a Expr > {
    self.print_get_values_with( exprs, info.clone() ) ? ;
    self.parse_get_values_with(info)
  }

  /// Check-sat with assumptions command with unit info.
  fn print_check_sat_assuming<'a, Ident, Idents>(
    & mut self, bool_vars: Idents
  ) -> SmtRes<()>
  where
  Ident: ?Sized + Sym2Smt<()> + 'a,
  Idents: Copy + IntoIterator< Item = & 'a Ident > {
    self.print_check_sat_assuming_with(bool_vars, ())
  }

  /// Check-sat with assumptions command.
  fn print_check_sat_assuming_with<'a, Info, Ident, Idents>(
    & mut self, bool_vars: Idents, info: Info
  ) -> SmtRes<()>
  where
  Info: Copy,
  Ident: ?Sized + Sym2Smt<Info> + 'a,
  Idents: Copy + IntoIterator< Item = & 'a Ident > {
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
  fn check_sat_assuming<'a, Ident, Idents>(
    & mut self, idents: Idents
  ) -> SmtRes<bool>
  where
  Ident: ?Sized + Sym2Smt<()> + 'a,
  Idents: Copy + IntoIterator< Item = & 'a Ident > {
    self.check_sat_assuming_with(idents, ())
  }

  /// Check-sat assuming command, turns `unknown` results into errors.
  fn check_sat_assuming_with<'a, Info, Ident, Idents>(
    & mut self, idents: Idents, info: Info
  ) -> SmtRes<bool>
  where
  Info: Copy,
  Ident: ?Sized + Sym2Smt<Info> + 'a,
  Idents: Copy + IntoIterator< Item = & 'a Ident > {
    self.print_check_sat_assuming_with(idents, info) ? ;
    self.parse_check_sat()
  }

  /// Check-sat assuming command, turns `unknown` results into `None`.
  fn check_sat_assuming_or_unknown_u<'a, Ident, Idents>(
    & mut self, idents: Idents
  ) -> SmtRes<Option<bool>>
  where
  Ident: ?Sized + Sym2Smt<()> + 'a,
  Idents: Copy + IntoIterator< Item = & 'a Ident > {
    self.check_sat_assuming_or_unknown(idents, ())
  }

  /// Check-sat assuming command, turns `unknown` results into `None`.
  fn check_sat_assuming_or_unknown<'a, Info, Ident, Idents>(
    & mut self, idents: Idents, info: Info
  ) -> SmtRes<Option<bool>>
  where
  Info: Copy,
  Ident: ?Sized + Sym2Smt<Info> + 'a,
  Idents: Copy + IntoIterator< Item = & 'a Ident > {
    self.print_check_sat_assuming_with(idents, info) ? ;
    self.parse_check_sat_or_unknown()
  }
}