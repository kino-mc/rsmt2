//! Wrapper around an SMT Lib 2 compliant solver.
//!
//! The underlying solver runs in a separate process, communication goes
//! through system pipes. 

use std::fs::File ;
use std::process::{
  Child, ChildStdin, Command, Stdio
} ;
use std::io::{ Write, BufWriter, BufReader } ;

use errors::* ;

use common::* ;
use conf::SolverConf ;
use parse::{ IdentParser, ValueParser, ExprParser, RSmtParser } ;





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





/// Solver providing most of the SMT-LIB 2.5 commands.
///
/// Note the [`tee` function][tee fun], which takes a file writer to which it
/// will write everything sent to the solver.
///
/// [tee fun]: #method.tee (tee function)
pub struct Solver<Parser> {
  /// Solver configuration.
  conf: SolverConf,
  /// Actual solver process.
  kid: Child,
  /// Solver's stdin.
  stdin: BufWriter<ChildStdin>,
  /// Tee file writer.
  tee: Option< BufWriter<File> >,
  /// Parser on the solver's stdout.
  smt_parser: RSmtParser,
  /// User-defined parser.
  parser: Parser,
  /// Actlit counter.
  actlit: usize,
}

/// Tries to write something in the solver.
macro_rules! wrt {
  ($slf:expr, |$w:ident| $($tail:tt)*) => ({
    if let Some(ref mut $w) = $slf.tee {
      { $($tail)* }
      $w.flush() ?
    }
    let $w = & mut $slf.stdin ;
    { $($tail)* }
    $w.flush() ?
  }) ;
}

impl<Parser> ::std::ops::Drop for Solver<Parser> {
  fn drop(& mut self) {
    let _ = self.kill() ;
    ()
  }
}

impl<Parser> Solver<Parser> {
  /// Constructor.
  pub fn new(conf: SolverConf, parser: Parser) -> SmtRes<Self> {
    let cmd = conf.get_cmd().to_string() ;

    // Constructing command and spawning kid.
    let mut kid = Command::new(
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
    ).spawn().chain_err::<_, ErrorKind>(
      || format!(
        "While spawning child process with {}", cmd
      ).into()
    ) ? ;

    let mut stdin_opt = None ;
    ::std::mem::swap( & mut stdin_opt, & mut kid.stdin ) ;

    let stdin = if let Some(inner) = stdin_opt {
      BufWriter::new(inner)
    } else {
      bail!("could not retrieve solver's stdin")
    } ;

    let mut stdout_opt = None ;
    ::std::mem::swap( & mut stdout_opt, & mut kid.stdout ) ;

    let smt_parser = if let Some(inner) = stdout_opt {
      RSmtParser::new( BufReader::new(inner) )
    } else {
      bail!("could not retrieve solver's stdin")
    } ;

    let tee = None ;
    let actlit = 0 ;

    Ok(
      Solver {
        kid, stdin, tee, conf, smt_parser, parser, actlit,
      }
    )
  }
  /// Creates a solver kid with the default configuration.
  ///
  /// Mostly used in tests, same as `Self::new( SolverConf::z3(), parser )`.
  pub fn default(parser: Parser) -> SmtRes<Self> {
    Self::new( SolverConf::z3(), parser )
  }

  /// Configuration of the solver.
  pub fn conf(& self) -> & SolverConf { & self.conf }

  /// Forces the solver to write all communications to a file.
  ///
  /// Errors if the solver was already tee-ed.
  pub fn tee(& mut self, file: File) -> SmtRes<()> {
    if self.tee.is_some() {
      bail!("Trying to tee a solver that's already tee-ed")
    }
    self.tee = Some(
      BufWriter::with_capacity(1000, file)
    ) ;
    Ok(())
  }

  /// True if the solver is tee-ed.
  pub fn is_teed(& self) -> bool { self.tee.is_some() }

  /// Kills the solver kid.
  ///
  /// The windows version just prints `(exit)\n` on the kid's `stdin`. Anything
  /// else seems to cause problems.
  #[cfg(windows)]
  pub fn kill(& mut self) -> SmtRes<()> {
    if let Some(stdin) = self.kid.stdin.as_mut() {
      let _ = writeln!(stdin, "(exit)\n") ;
    }
    Ok(())
  }
  /// Kills the solver kid.
  ///
  /// The windows version just prints `(exit)\n` on the kid's `stdin`. Anything
  /// else seems to cause problems.
  #[cfg(not(windows))]
  pub fn kill(& mut self) -> SmtRes<()> {
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

  /// True if no actlits have been created since the last reset.
  #[inline]
  fn has_actlits(& self) -> bool { self.actlit > 0 }

  /// Introduces a new actlit.
  #[inline]
  pub fn get_actlit(& mut self) -> SmtRes<Actlit> {
    let id = self.actlit ;
    self.actlit += 1 ;
    let next_actlit = Actlit { id } ;
    wrt! {
      self, |w| write!(
        w, "(declare-fun {}{}{} () Bool)",
        actlit_pref, next_actlit.id, actlit_suff
      ) ?
    }
    Ok(next_actlit)
  }

  /// Deactivates an activation literal, alias for
  /// `solver.set_actlit(actlit, false)`.
  #[inline]
  pub fn de_actlit(& mut self, actlit: Actlit) -> SmtRes<()> {
    self.set_actlit(actlit, false)
  }

  /// Forces the value of an actlit and consumes it.
  #[inline]
  pub fn set_actlit(
    & mut self, actlit: Actlit, b: bool
  ) -> SmtRes<()> {
    wrt! {
      self, |w| {
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
      }
    }
    Ok(())
  }


  /// Prints a comment in the tee-ed file if any.
  ///
  /// Inserts a newline at the end of the comment.
  #[inline]
  pub fn comment(& mut self, args: ::std::fmt::Arguments) -> SmtRes<()> {
    if let Some(ref mut file) = self.tee {
      file.write_all( "; ".as_bytes() ) ? ;
      file.write_fmt(args) ? ;
      file.write_all( "\n".as_bytes() ) ? ;
      file.flush() ?
    }
    Ok(())
  }




  // |===| Introducing new symbols.

  /// Declares a new sort.
  #[inline]
  pub fn declare_sort<Sort>(
    & mut self, sort: & Sort, arity: & u8
  ) -> SmtRes<()>
  where Sort: Sort2Smt {
    wrt! {
      self, |w| {
        write_str(w, "(declare-sort ") ? ;
        sort.sort_to_smt2(w) ? ;
        write!(w, " {})\n", arity) ?
      }
    }
    Ok(())
  }

  /// Defines a new sort.
  #[inline]
  pub fn define_sort<'a, Sort, Arg, Args, Body>(
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
  pub fn define_sort_with<'a, Sort, Info, Arg, Args, Body>(
    & mut self, sort: & Sort, args: Args, body: & Body, info: Info
  ) -> SmtRes<()>
  where
  Info: Copy,
  Sort: Sort2Smt,
  Arg: Expr2Smt<Info> + 'a,
  Body: Expr2Smt<Info>,
  Args: Copy + IntoIterator< Item = & 'a Arg > {
    wrt!{
      self, |w| {
        write_str(w, "( define-sort ") ? ;
        sort.sort_to_smt2(w) ? ;
        write_str(w, "\n   ( ") ? ;
        for arg in args {
          arg.expr_to_smt2(w, info) ? ;
          write_str(w, " ") ?
        }
        write_str(w, ")\n   ") ? ;
        body.expr_to_smt2(w, info) ? ;
        write_str(w, "\n)\n") ?
      }
    }
    Ok(())
  }

  /// Declares a new function symbol.
  #[inline]
  pub fn declare_fun<'a, FunSym, ArgSort, Args, OutSort> (
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
  pub fn declare_fun_with<'a, Info, FunSym, ArgSort, Args, OutSort> (
    & mut self, symbol: & FunSym, args: Args, out: & OutSort, info: Info
  ) -> SmtRes<()>
  where
  Info: Copy,
  FunSym: ?Sized + Sym2Smt<Info>,
  ArgSort: ?Sized + Sort2Smt + 'a,
  OutSort: ?Sized + Sort2Smt,
  Args: Copy + IntoIterator< Item = & 'a ArgSort > {
    wrt! {
      self, |w| {
        write_str(w, "(declare-fun ") ? ;
        symbol.sym_to_smt2(w, info) ? ;
        write_str(w, " ( ") ? ;
        for arg in args.into_iter() {
          arg.sort_to_smt2(w) ? ;
          write_str(w, " ") ?
        }
        write_str(w, ") ") ? ;
        out.sort_to_smt2(w) ? ;
        write_str(w, ")\n") ?
      }
    }
    Ok(())
  }

  /// Declares a new constant.
  #[inline]
  pub fn declare_const<Sym, Sort> (
    & mut self, symbol: & Sym, out_sort: & Sort
  ) -> SmtRes<()>
  where Sym: ?Sized + Sym2Smt<()>, Sort: ?Sized + Sort2Smt {
    self.declare_const_with(symbol, out_sort, ())
  }

  /// Declares a new constant.
  #[inline]
  pub fn declare_const_with<Info, Sym, Sort> (
    & mut self, symbol: & Sym, out_sort: & Sort, info: Info
  ) -> SmtRes<()>
  where Info: Copy, Sym: ?Sized + Sym2Smt<Info>, Sort: ?Sized + Sort2Smt {
    wrt! {
      self, |w| {
        write_str(w, "(declare-const ") ? ;
        symbol.sym_to_smt2(w, info) ? ;
        write_str(w, " ") ? ;
        out_sort.sort_to_smt2(w) ? ;
        write_str(w, ")\n") ?
      }
    }
    Ok(())
  }

  /// Defines a new function symbol.
  #[inline]
  pub fn define_fun<
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
  pub fn define_fun_with<
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
    wrt! {
      self, |w| {
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
        write_str(w, "\n)\n") ?
      }
    }
    Ok(())
  }

  /// Defines some new (possibily mutually) recursive functions.
  #[inline]
  pub fn define_funs_rec<
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
  pub fn define_funs_rec_with<
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
    wrt! {
      self, |w| {
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
        write_str(w, "\n )\n)\n") ?
      }
    }
    Ok(())
  }

  /// Defines a new recursive function.
  #[inline]
  pub fn define_fun_rec<
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
  pub fn define_fun_rec_with<
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
    wrt! {
      self, |w| {
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
        write_str(w, "\n )\n)\n") ?
      }
    }
    Ok(())
  }


  // |===| (Re)starting and terminating.

  /// Shuts the solver down.
  #[inline]
  pub fn exit(& mut self) -> SmtRes<()> {
    wrt! {
      self, |w| write_str(w, "(exit)\n") ?
    }
    Ok(())
  }

  /// Resets the underlying solver. Restarts the kid process if no reset
  /// command is supported.
  #[inline]
  pub fn reset(
    & mut self
  ) -> SmtRes<()> {
    self.actlit = 0 ;
    wrt! {
      self, |w| write_str(w, "(reset)\n") ?
    }
    Ok(())
  }

  /// Sets the logic.
  #[inline]
  pub fn set_logic(
    & mut self, logic: Logic
  ) -> SmtRes<()> {
    wrt! {
      self, |w| {
        write_str(w, "(set-logic ") ? ;
        logic.to_smt2(w, ()) ? ;
        write_str(w, ")\n") ?
      }
    }
    Ok(())
  }

  /// Set option command.
  #[inline]
  pub fn set_option<Value: ::std::fmt::Display>(
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
    wrt! {
      self, |w| write!(
        w, "(set-option {} {})\n", option, value
      ) ?
    }
    Ok(())
  }

  /// Activates unsat core production.
  #[inline]
  pub fn produce_unsat_core(& mut self) -> SmtRes<()> {
    self.set_option( ":produce-unsat-cores", "true" )
  }


  // |===| Modifying the assertion stack.

  /// Pushes `n` layers on the assertion stack.
  #[inline]
  pub fn push(& mut self, n: u8) -> SmtRes<()> {
    wrt! {
      self, |w| write!(w, "(push {})\n", n) ?
    }
    Ok(())
  }
  /// Pops `n` layers off the assertion stack.
  #[inline]
  pub fn pop(& mut self, n: u8) -> SmtRes<()> {
    wrt! {
      self, |w| write!(w, "(pop {})\n", n) ?
    }
    Ok(())
  }
  /// Resets the assertions in the solver.
  #[inline]
  pub fn reset_assertions(& mut self) -> SmtRes<()> {
    wrt! {
      self, |w| write_str(w, "(reset-assertions)\n") ?
    }
    Ok(())
  }


  // // |===| Inspecting settings.

  // /// Get info command.
  // #[inline]
  // pub fn get_info(& mut self, flag: & str) -> SmtRes<()> {
  //   wrt! {
  //     self, |w| write!(w, "(get-info {})\n", flag) ?
  //   }
  //   Ok(())
  // }
  // /// Get option command.
  // #[inline]
  // pub fn get_option(& mut self, option: & str) -> SmtRes<()> {
  //   wrt! {
  //     self, |w| write!(w, "(get-option {})\n", option) ?
  //   }
  //   Ok(())
  // }



  // |===| Script information.

  /// Set info command.
  #[inline]
  pub fn set_info(& mut self, attribute: & str) -> SmtRes<()> {
    wrt! {
      self, |w| write!(w, "(set-info {})\n", attribute) ?
    }
    Ok(())
  }
  /// Echo command.
  #[inline]
  pub fn echo(& mut self, text: & str) -> SmtRes<()> {
    wrt! {
      self, |w| write!(w, "(echo \"{}\")\n", text) ?
    }
    Ok(())
  }



  /// Check-sat command.
  #[inline]
  pub fn print_check_sat(& mut self) -> SmtRes<()> {
    wrt! {
      self, |w| write_str(w, "(check-sat)\n") ?
    }
    Ok(())
  }
  /// Check-sat command, with actlits.
  #[inline]
  pub fn print_check_sat_act<'a, Actlits>(
    & mut self, actlits: Actlits
  ) -> SmtRes<()>
  where
  Actlits: Copy + IntoIterator<Item = & 'a Actlit> {
    wrt! {
      self, |w| {
        write_str(w, "(check-sat") ? ;
        for actlit in actlits {
          write!(w, " ") ? ;
          actlit.write(w) ?
        }
        write_str(w, ")\n") ?
      }
    }
    Ok(())
  }


  // |===| Asserting and inspecting formulas.

  /// Asserts an expression without print information.
  #[inline]
  pub fn assert<Expr>(
    & mut self, expr: & Expr
  ) -> SmtRes<()>
  where Expr: ?Sized + Expr2Smt<()> {
    self.assert_with(expr, ())
  }

  /// Asserts an expression without print information, guarded by an activation
  /// literal.
  #[inline]
  pub fn assert_act<Expr>(
    & mut self, actlit: & Actlit, expr: & Expr
  ) -> SmtRes<()>
  where Expr: ?Sized + Expr2Smt<()> {
    self.assert_act_with(actlit, expr, ())
  }

  /// Asserts an expression with some print information.
  #[inline]
  pub fn assert_with<Info, Expr>(
    & mut self, expr: & Expr, info: Info
  ) -> SmtRes<()>
  where
  Info: Copy,
  Expr: ?Sized + Expr2Smt<Info> {
    wrt! {
      self, |w| {
        write_str(w, "(assert\n  ") ? ;
        expr.expr_to_smt2(w, info) ? ;
        write_str(w, "\n)\n") ?
      }
    }
    Ok(())
  }

  /// Asserts an expression with some print information, guarded by an
  /// activation literal.
  #[inline]
  pub fn assert_act_with<Info, Expr>(
    & mut self, actlit: & Actlit, expr: & Expr, info: Info
  ) -> SmtRes<()>
  where
  Info: Copy,
  Expr: ?Sized + Expr2Smt<Info>, {
    wrt! {
      self, |w| {
        write_str(w, "(assert\n  (=>\n    ") ? ;
        actlit.write(w) ? ;
        write_str(w, "\n    ") ? ;
        expr.expr_to_smt2(w, info) ? ;
        write_str(w, "\n  )\n)\n") ?
      }
    }
    Ok(())
  }




  /// Get-model command.
  #[inline]
  pub fn print_get_model(& mut self) -> SmtRes<()> {
    wrt! {
      self, |w| write_str(w, "(get-model)\n") ?
    }
    Ok(())
  }

  /// Parse the result of a check-sat, turns `unknown` results into errors.
  #[inline]
  pub fn parse_check_sat(& mut self) -> SmtRes<bool> {
    if let Some(res) = self.smt_parser.check_sat() ? {
      Ok(res)
    } else {
      Err( ErrorKind::Unknown.into() )
    }
  }

  /// Parse the result of a check-sat, turns `unknown` results into `None`.
  #[inline]
  pub fn parse_check_sat_or_unknown(& mut self) -> SmtRes< Option<bool> > {
    self.smt_parser.check_sat()
  }

  /// Check-sat command, turns `unknown` results into errors.
  pub fn check_sat(& mut self) -> SmtRes<bool> {
    self.print_check_sat() ? ;
    self.parse_check_sat()
  }
  /// Check-sat command with activation literals, turns `unknown` results into
  /// errors.
  pub fn check_sat_act<'a, Actlits>(
    & mut self, actlits: Actlits
  ) -> SmtRes<bool>
  where
  Actlits: Copy + IntoIterator<Item = & 'a Actlit> {
    self.print_check_sat_act(actlits) ? ;
    self.parse_check_sat()
  }

  /// Check-sat command, turns `unknown` results in `None`.
  pub fn check_sat_or_unknown(& mut self) -> SmtRes< Option<bool> > {
    self.print_check_sat() ? ;
    self.parse_check_sat_or_unknown()
  }
  /// Check-sat command with activation literals, turns `unknown` results in
  /// `None`.
  pub fn check_sat_act_or_unknown<'a, Actlits>(
    & mut self, actlits: Actlits
  ) -> SmtRes< Option<bool> >
  where
  Actlits: Copy + IntoIterator<Item = & 'a Actlit> {
    self.print_check_sat_act(actlits) ? ;
    self.parse_check_sat_or_unknown()
  }

  /// Get-assertions command.
  pub fn print_get_assertions(& mut self) -> SmtRes<()> {
    wrt! {
      self, |w| write_str(w, "(get-assertions)\n") ?
    }
    Ok(())
  }
  /// Get-assignment command.
  pub fn print_get_assignment(& mut self) -> SmtRes<()> {
    wrt! {
      self, |w| write_str(w, "(get-assignment)\n") ?
    }
    Ok(())
  }
  /// Get-unsat-assumptions command.
  pub fn print_get_unsat_assumptions(& mut self) -> SmtRes<()> {
    wrt! {
      self, |w| write_str(w, "(get-unsat-assumptions)\n") ?
    }
    Ok(())
  }
  /// Get-proof command.
  pub fn print_get_proof(& mut self) -> SmtRes<()> {
    wrt! {
      self, |w| write_str(w, "(get-proof)\n") ?
    }
    Ok(())
  }
  /// Get-unsat-core command.
  pub fn print_get_unsat_core(& mut self) -> SmtRes<()> {
    wrt! {
      self, |w| write_str(w, "(get-unsat-core)\n") ?
    }
    Ok(())
  }

  /// Get-values command.
  pub fn print_get_values<'a, Expr, Exprs>(
    & mut self, exprs: Exprs
  ) -> SmtRes<()>
  where
  Expr: ?Sized + Expr2Smt<()> + 'a,
  Exprs: Clone + IntoIterator< Item = & 'a Expr > {
    self.print_get_values_with(exprs, ())
  }

  /// Get-values command.
  pub fn print_get_values_with<'a, Info, Expr, Exprs>(
    & mut self, exprs: Exprs, info: Info
  ) -> SmtRes<()>
  where
  Info: Copy,
  Expr: ?Sized + Expr2Smt< Info > + 'a,
  Exprs: Clone + IntoIterator< Item = & 'a Expr > {
    wrt! {
      self, |w| {
        write!(w, "(get-value (") ? ;
        for e in exprs.clone() {
          write_str(w, "\n  ") ? ;
          e.expr_to_smt2(w, info) ?
        }
        write_str(w, "\n) )\n") ?
      }
    }
    Ok(())
  }

  /// Check-sat with assumptions command with unit info.
  pub fn print_check_sat_assuming<'a, Ident, Idents>(
    & mut self, bool_vars: Idents
  ) -> SmtRes<()>
  where
  Ident: ?Sized + Sym2Smt<()> + 'a,
  Idents: Copy + IntoIterator< Item = & 'a Ident > {
    self.print_check_sat_assuming_with(bool_vars, ())
  }

  /// Check-sat with assumptions command.
  pub fn print_check_sat_assuming_with<'a, Info, Ident, Idents>(
    & mut self, bool_vars: Idents, info: Info
  ) -> SmtRes<()>
  where
  Info: Copy,
  Ident: ?Sized + Sym2Smt<Info> + 'a,
  Idents: Copy + IntoIterator< Item = & 'a Ident > {
    match * self.conf.get_check_sat_assuming() {
      Some(ref cmd) => {
        wrt! {
          self, |w| {
            write!(w, "({}\n ", cmd) ? ;
            for sym in bool_vars {
              write_str(w, " ") ? ;
              sym.sym_to_smt2(w, info) ?
            } ;
            write_str(w, "\n)\n") ?
          }
        }
        Ok(())
      },
      _ => Err(
        format!(
          "check-sat-assuming is not supported for {}",
          self.conf.style()
        ).into()
      ),
    }
  }

  /// Check-sat assuming command, turns `unknown` results into errors.
  pub fn check_sat_assuming<'a, Ident, Idents>(
    & mut self, idents: Idents
  ) -> SmtRes<bool>
  where
  Ident: ?Sized + Sym2Smt<()> + 'a,
  Idents: Copy + IntoIterator< Item = & 'a Ident > {
    self.check_sat_assuming_with(idents, ())
  }

  /// Check-sat assuming command, turns `unknown` results into errors.
  pub fn check_sat_assuming_with<'a, Info, Ident, Idents>(
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
  pub fn check_sat_assuming_or_unknown_u<'a, Ident, Idents>(
    & mut self, idents: Idents
  ) -> SmtRes<Option<bool>>
  where
  Ident: ?Sized + Sym2Smt<()> + 'a,
  Idents: Copy + IntoIterator< Item = & 'a Ident > {
    self.check_sat_assuming_or_unknown(idents, ())
  }

  /// Check-sat assuming command, turns `unknown` results into `None`.
  pub fn check_sat_assuming_or_unknown<'a, Info, Ident, Idents>(
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


impl<Parser: Copy> Solver<Parser> {

  /// Parse the result of a get-model.
  pub fn parse_get_model<Ident, Type, Value>(
    & mut self
  ) -> SmtRes<Vec<(Ident, Vec<Type>, Type, Value)>>
  where
  Parser: for<'a> IdentParser<Ident, Type, & 'a mut RSmtParser> +
          for<'a> ValueParser<Value, & 'a mut RSmtParser> {
    let has_actlits = self.has_actlits() ;
    self.smt_parser.get_model(has_actlits, self.parser)
  }

  /// Get-model command.
  pub fn get_model<Ident, Type, Value>(
    & mut self
  ) -> SmtRes<Vec<(Ident, Vec<Type>, Type, Value)>>
  where
  Parser: for<'a> IdentParser<Ident, Type, & 'a mut RSmtParser> +
          for<'a> ValueParser<Value, & 'a mut RSmtParser> {
    self.print_get_model() ? ;
    self.parse_get_model()
  }

  /// Parse the result of a get-model where all the symbols are nullary.
  pub fn parse_get_model_const<Ident, Type, Value>(
    & mut self
  ) -> SmtRes<Vec<(Ident, Type, Value)>>
  where
  Parser: for<'a> IdentParser<Ident, Type, & 'a mut RSmtParser> +
          for<'a> ValueParser<Value, & 'a mut RSmtParser> {
    let has_actlits = self.has_actlits() ;
    self.smt_parser.get_model_const(has_actlits, self.parser)
  }

  /// Get-model command when all the symbols are nullary.
  pub fn get_model_const<Ident, Type, Value>(
    & mut self
  ) -> SmtRes<Vec<(Ident, Type, Value)>>
  where
  Parser: for<'a> IdentParser<Ident, Type, & 'a mut RSmtParser> +
          for<'a> ValueParser<Value, & 'a mut RSmtParser> {
    self.print_get_model() ? ;
    self.parse_get_model_const()
  }

  /// Parse the result of a get-values.
  pub fn parse_get_values<Expr, Value>(
    & mut self
  ) -> SmtRes<Vec<(Expr, Value)>>
  where
  Parser: for<'a> ExprParser<Expr, (), & 'a mut RSmtParser> +
          for<'a> ValueParser<Value, & 'a mut RSmtParser> {
    self.parse_get_values_with(())
  }

  /// Parse the result of a get-values.
  pub fn parse_get_values_with<Info, Expr, Value>(
    & mut self, info: Info
  ) -> SmtRes<Vec<(Expr, Value)>>
  where
  Info: Copy,
  Parser: for<'a> ExprParser<Expr, Info, & 'a mut RSmtParser> +
          for<'a> ValueParser<Value, & 'a mut RSmtParser> {
    self.smt_parser.get_values(self.parser, info)
  }

  /// Get-values command.
  ///
  /// Notice that the input expression type and the output one have no reason
  /// to be the same.
  pub fn get_values<'a, Expr, Exprs, PExpr, PValue>(
    & mut self, exprs: Exprs
  ) -> SmtRes<Vec<(PExpr, PValue)>>
  where
  Parser: for<'b> ExprParser<PExpr, (), & 'b mut RSmtParser> +
          for<'b> ValueParser<PValue, & 'b mut RSmtParser>,
  Expr: ?Sized + Expr2Smt<()> + 'a,
  Exprs: Copy + IntoIterator< Item = & 'a Expr > {
    self.get_values_with(exprs, ())
  }

  /// Get-values command.
  ///
  /// Notice that the input expression type and the output one have no reason
  /// to be the same.
  pub fn get_values_with<
    'a, Info, Expr, Exprs, PExpr, PValue
  >(
    & mut self, exprs: Exprs, info: Info
  ) -> SmtRes<Vec<(PExpr, PValue)>>
  where
  Info: Copy,
  Parser: for<'b> ExprParser<PExpr, Info, & 'b mut RSmtParser> +
          for<'b> ValueParser<PValue, & 'b mut RSmtParser>,
  Expr: ?Sized + Expr2Smt<Info> + 'a,
  Exprs: Copy + IntoIterator< Item = & 'a Expr > {
    self.print_get_values_with( exprs, info.clone() ) ? ;
    self.parse_get_values_with(info)
  }

}
