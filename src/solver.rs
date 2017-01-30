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


macro_rules! wrap {
  ($e:expr) => (
    {
      use nom::IResult::* ;
      use std::str::from_utf8 ;
      match $e {
        Done(rest, res) => match from_utf8(rest) {
          Ok(s) => (s.to_string(), res),
          Err(e) => (
            String::new(), Err(e).chain_err(
              || ErrorKind::IoError(
                "could not convert remaining bytes to utf8".into()
              )
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

/// Wraps errors (if any) into `IoError`s and early-returns.
#[macro_export]
macro_rules! smtry_io {
  ($info:expr => $e:expr $(;)*) => (
    match $e {
      Ok(something) => something,
      e => return e.chain_err(
        || $crate::ErrorKind::IoError(
          format!("while {}", $info)
        )
      ),
    }
  ) ;
  ( $info:expr => $e:expr ; $($tail:tt)+ ) => (
    match $e {
      Ok(()) => smtry_io!( $info => $( $tail )+ ),
      e => return e.chain_err(
        || $crate::ErrorKind::IoError(
          format!("while {}", $info)
        )
      ),
    }
  ) ;
}

/// Wraps errors (if any) into `IoError`s and (**not-early-**)returns the
/// first error, if any.
#[macro_export]
macro_rules! smt_cast_io {
  ($info:expr => $e:expr $(;)*) => (
    $e.chain_err(
      || $crate::ErrorKind::IoError(
        format!("while {}", $info)
      )
    )
  ) ;
  ( $info:expr => $e:expr ; $( $tail:tt )+ ) => (
    match $e {
      Ok(()) => smt_cast_io!( $info => $( $tail )* ),
      err => err.chain_err(
        || $crate::ErrorKind::IoError(
          format!("while {}", $info)
        )
      )
    }
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
      try!(
        smt_cast_io!(
          "reading solver's output" => buff.read_line(
            & mut $slf.buff
          )
        )
      ) ;
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
  pub fn mk(conf: SolverConf) -> Res<Self> {
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
    ).chain_err(
      || ErrorKind::IoError(
        "while spawning child process".into()
      )
    )
  }
  /// Kills the solver kid.
  pub fn kill(mut self) -> Res<()> {
    self.kid.kill().chain_err(
      || ErrorKind::IoError(
        "while killing child process".into()
      )
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
  pub fn mk(kid: & 'kid mut Kid, parser: Parser) -> Res<Self> {
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
    F: Fn(& mut Write) -> Res<()>
  >(& mut self, f: F) -> Res<()> {
    try!( f(& mut self.stdin) ) ;
    smtry_io!(
      "flushing solver's stdin" => self.stdin.flush()
    ) ;
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


impl<
  'kid, Parser: ParseSmt2 + 'static
> Query<'kid, Parser> for PlainSolver<'kid, Parser> {}

impl<
  'kid, Parser: ParseSmt2 + 'static, Info, Ident: Sym2Smt<Info>
> QueryIdent<
  'kid, Parser, Info, Ident
> for PlainSolver<'kid, Parser> {}

impl<
  'kid, Parser: ParseSmt2 + 'static, Info, Expr: Expr2Smt<Info>
> QueryExpr<
  'kid, Parser, Info, Expr
> for PlainSolver<'kid, Parser> {}

impl<
  'kid, Parser: ParseSmt2 + 'static, Expr: Expr2Smt<Parser::I>
> QueryExprInfo<
  'kid, Parser, Expr
> for PlainSolver<'kid, Parser> {}











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
      smtry_io!(
        "writing comment header to tee file" => write!(self.file, ";; ")
      ),
      c => smtry_io!(
        "writing fetched data to tee file" => write!( self.file, "{}", c)
      )
    )
  }
  /// Applies a function to the writer on the solver's stdin.
  fn write<
    F: Fn(& mut Write) -> Res<()>
  >(& mut self, f: F) -> Res<()> {
    try!( f(& mut self.solver.stdin) ) ;
    smtry_io!(
      "flushing (tee) solver's stdin" => self.solver.stdin.flush()
    ) ;
    smtry_io!(
      "writing newline to tee file" => write!(self.file, "\n")
    ) ;
    try!( f(& mut self.file) ) ;
    smtry_io!(
      "flushing tee file" => self.file.flush()
    ) ;
    Ok(())
  }
  fn comment(& mut self, txt: & str) -> Res<()> {
    for line in txt.lines() {
      smtry_io!(
        "writing comment to tee file" => write!(self.file, ";; {}", line)
      )
    } ;
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


impl<
  'kid, Parser: ParseSmt2 + 'static
> Query<'kid, Parser> for TeeSolver<'kid, Parser> {}

impl<
  'kid, Parser: ParseSmt2 + 'static, Info, Ident: Sym2Smt<Info>
> QueryIdent<
  'kid, Parser, Info, Ident
> for TeeSolver<'kid, Parser> {}

impl<
  'kid, Parser: ParseSmt2 + 'static, Info, Expr: Expr2Smt<Info>
> QueryExpr<
  'kid, Parser, Info, Expr
> for TeeSolver<'kid, Parser> {}

impl<
  'kid, Parser: ParseSmt2 + 'static, Expr: Expr2Smt<Parser::I>
> QueryExprInfo<
  'kid, Parser, Expr
> for TeeSolver<'kid, Parser> {}













/// Most basic function needed to provide SMT-LIB commands.
pub trait SolverBasic<'kid, Parser: ParseSmt2 + 'static> {
  /// Fetches data.
  fn fetch(& mut self) -> Res<()> ;
  /// Applies a function to the writer on the solver's stdin.
  fn write<
    F: Fn(& mut Write) -> Res<()>
  >(& mut self, f: F) -> Res<()> ;
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
  PlainSolver::mk(kid, parser)
}







/// Provides SMT-LIB commands that are not queries.
pub trait Solver<'kid, Parser: ParseSmt2 + 'static> :
SolverPrims<'kid, Parser> {


  // |===| (Re)starting and terminating.

  /** Resets the underlying solver. Restarts the kid process if no reset
  command is supported. */
  #[inline(always)]
  fn reset(
    & mut self
  ) -> Res<()> {
    parse_success!(
      self for {
        self.write(
          |w| smt_cast_io!(
            "writing reset command" => write!(w, "(reset)\n")
          )
        )
      }
    )
  }



  /** Sets the logic. */
  #[inline]
  fn set_logic(
    & mut self, logic: & Logic
  ) -> Res<()> {
    parse_success!(
      self for {
        self.write(
          |w| smt_cast_io!(
            "writing set logic command" =>
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
        self.write(
          |w| smt_cast_io!(
            format!(
              "writing set option command ({}: {})", option, value
            ) => write!(
              w, "(set-option {} {})\n", option, value
            )
          )
        )
      }
    )
  }
  /** Activates interactive mode. */
  #[inline(always)]
  fn interactive_mode(& mut self) -> Res<()> {
    parse_success!(
      self for {
        self.write(
          |w| smt_cast_io!(
            "writing set option command on interactive mode (true)" =>
              write!(w, "(set-option :interactive-mode true)\n")
          )
        )
      }
    )
  }
  /** Activates print success. */
  #[inline(always)]
  fn print_success(& mut self) -> Res<()> {
    parse_success!(
      self for {
        self.write(
          |w| smt_cast_io!(
            "writing set option command on print success (true)" => write!(
              w, "(set-option :print-success true)\n"
            )
          )
        )
      }
    )
  }
  /** Activates unsat core production. */
  #[inline(always)]
  fn produce_unsat_core(& mut self) -> Res<()> {
    parse_success!(
      self for {
        self.write(
          |w| smt_cast_io!(
            "writing set option command on produce unsat cores (true)" =>
              write!(w, "(set-option :produce-unsat-cores true)\n")
          )
        )
      }
    )
  }
  /** Shuts the solver down. */
  #[inline(always)]
  fn exit(& mut self) -> Res<()> {
    parse_success!(
      self for {
        self.write(
          |w| smt_cast_io!(
            "writing exit command" => write!(w, "(exit)\n")
          )
        )
      }
    )
  }


  // |===| Modifying the assertion stack.

  /** Pushes `n` layers on the assertion stack. */
  #[inline(always)]
  fn push(& mut self, n: & u8) -> Res<()> {
    parse_success!(
      self for {
        self.write(
          |w| smt_cast_io!(
            format!("writing push ({}) command", n) => write!(
              w, "(push {})\n", n
            )
          )
        )
      }
    )
  }
  /** Pops `n` layers off the assertion stack. */
  #[inline(always)]
  fn pop(& mut self, n: & u8) -> Res<()> {
    parse_success!(
      self for {
        self.write(
          |w| smt_cast_io!(
            format!("writing pop ({}) command", n) => write!(
              w, "(pop {})\n", n
            )
          )
        )
      }
    )
  }
  /** Resets the assertions in the solver. */
  #[inline(always)]
  fn reset_assertions(& mut self) -> Res<()> {
    parse_success!(
      self for {
        self.write(
          |w| smt_cast_io!(
            format!("writing reset assertions command") => write!(
              w, "(reset-assertions)\n"
            )
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
  ) -> Res<()> {
    parse_success!(
      self for {
        self.write(
          |w| smt_cast_io!(
            "writing declare sort command" =>
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
  ) -> Res<()> {
    let err_info = "writing define sort command" ;
    parse_success!(
      self for {
        self.write(
          |w| {
            smtry_io!( err_info =>
              write!(w, "( define-sort ") ;
              sort.sort_to_smt2(w) ;
              write!(w, "\n   ( ")
            ) ;
            for arg in args {
              smtry_io!( err_info =>
                arg.expr_to_smt2(w, info) ;
                write!(w, " ")
              ) ;
            } ;
            smt_cast_io!( err_info =>
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
  ) -> Res<()> {
    let err_info = "writing declare fun command" ;
    parse_success!(
      self for {
        self.write(
          |w| {
            smtry_io!( err_info =>
              write!(w, "(declare-fun ") ;
              symbol.sym_to_smt2(w, info) ;
              write!(w, " ( ")
            ) ;
            for arg in args {
              smtry_io!( err_info =>
                arg.sort_to_smt2(w) ;
                write!(w, " ")
              ) ;
            } ;
            smt_cast_io!( err_info =>
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
  ) -> Res<()> {
    parse_success!(
      self for {
        self.write(
          |w| smt_cast_io!(
            "writing declare const command" =>
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
  ) -> Res<()> {
    let err_info = "writing define fun command" ;
    parse_success!(
      self for {
        self.write(
          |w| {
            smtry_io!( err_info =>
              write!(w, "(define-fun ") ;
              symbol.sym_to_smt2(w, info) ;
              write!(w, " ( ")
            ) ;
            for arg in args {
              let (ref sym, ref sort) = * arg ;
              smtry_io!( err_info =>
                write!(w, "(") ;
                sym.sym_to_smt2(w, info) ;
                write!(w, " ") ;
                sort.sort_to_smt2(w) ;
                write!(w, ") ")
              )
            } ;
            smt_cast_io!( err_info =>
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
  ) -> Res<()> {
    let err_info = "writing define funs rec command" ;
    parse_success!(
      self for {
        self.write(
          |w| {
            // Header.
            smtry_io!( err_info => write!(w, "(define-funs-rec (\n") ) ;

            // Signatures.
            for fun in funs {
              let (ref sym, ref args, ref out, _) = * fun ;
              smtry_io!( err_info =>
                write!(w, "   (");
                sym.sym_to_smt2(w, info) ;
                write!(w, " ( ")
              ) ;
              for arg in * args {
                let (ref sym, ref sort) = * arg ;
                smtry_io!( err_info =>
                  write!(w, "(") ;
                  sym.sym_to_smt2(w, info) ;
                  write!(w, " ") ;
                  sort.sort_to_smt2(w) ;
                  write!(w, ") ")
                )
              } ;
              smtry_io!( err_info =>
                write!(w, ") ") ;
                out.sort_to_smt2(w) ;
                write!(w, ")\n")
              )
            } ;
            smtry_io!( err_info => write!(w, " ) (") ) ;

            // Bodies
            for fun in funs {
              let (_, _, _, ref body) = * fun ;
              smtry_io!( err_info =>
                write!(w, "\n   ") ;
                body.expr_to_smt2(w, info)
              )
            } ;
            smt_cast_io!( err_info => write!(w, "\n )\n)\n") )
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
  ) -> Res<()> {
    let err_info = "writing define fun rec command" ;
    parse_success!(
      self for {
        self.write(
          |w| {
            // Header.
            smtry_io!( err_info => write!(w, "(define-fun-rec (\n") ) ;

            // Signature.
            smtry_io!( err_info =>
              write!(w, "   (") ;
              symbol.sym_to_smt2(w, info) ;
              write!(w, " ( ")
            ) ;
            for arg in args {
              let (ref sym, ref sort) = * arg ;
              smtry_io!( err_info =>
                write!(w, "(") ;
                sym.sym_to_smt2(w, info) ;
                write!(w, " ") ;
                sort.sort_to_smt2(w) ;
                write!(w, ") ")
              )
            } ;
            smtry_io!( err_info =>
              write!(w, ") ") ;
              out.sort_to_smt2(w) ;
              write!(w, ")\n") ;
              write!(w, " ) (")
            ) ;

            // Body.
            smt_cast_io!( err_info =>
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
  ) -> Res<()> {
    parse_success!(
      self for {
        self.write(
          |w| smt_cast_io!(
            "writing assert command" =>
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
  fn get_info(& mut self, flag: & str) -> Res<()> {
    self.write(
      |w| smt_cast_io!(
        "writing get info command" => write!(w, "(get-info {})\n", flag)
      )
    )
  }
  /** Get option command. */
  #[inline(always)]
  fn get_option(& mut self, option: & str) -> Res<()> {
    self.write(
      |w| smt_cast_io!(
        format!("writing get option command ({})", option) =>
          write!(w, "(get-option {})\n", option) )
    )
  }

  // |===| Script information.

  /** Set info command. */
  #[inline(always)]
  fn set_info(& mut self, attribute: & str) -> Res<()> {
    self.write(
      |w| smt_cast_io!(
        format!("writing set option command ({})", attribute) =>
          write!(w, "(set-info {})\n", attribute) )
    )
  }
  /** Echo command. */
  #[inline(always)]
  fn echo(& mut self, text: & str) -> Res<()> {
    self.write(
      |w| smt_cast_io!(
        format!("writing echo command ({})", text) =>
        write!(w, "(echo \"{}\")\n", text)
      )
    )
  }


  // |===| Parsing simple stuff.

  /** Parse success. */
  #[inline]
  fn parse_success(& mut self) -> Res<()> {
    self.parse( |bytes, _| wrap!( success(bytes) ) )
  }
}







macro_rules! try_cast {
  ($e:expr) => (
    match $e {
      Ok(something) => something,
      Err(e) => return Err(e),
    }
  ) ;
}





/** Prints queries. */
pub trait Query<
  'kid, Parser: ParseSmt2 + 'static
> : Solver<'kid, Parser> {

  /** Check-sat command. */
  #[inline(always)]
  fn print_check_sat(& mut self) -> Res<()> {
    self.write(
      |w| smt_cast_io!(
        "writing check sat query" => write!(w, "(check-sat)\n")
      )
    )
  }

  /** Parse the result of a check-sat. */
  #[inline(always)]
  fn parse_check_sat(& mut self) -> Res<bool> {
    self.parse( |bytes, _| wrap!( check_sat(bytes) ) )
  }

  /** Check-sat command. */
  fn check_sat(& mut self) -> Res<bool> {
    try_cast!(
      self.print_check_sat()
    ) ;
    self.parse_check_sat()
  }

  /** Get-model command. */
  #[inline(always)]
  fn print_get_model(& mut self) -> Res<()> {
    self.write(
      |w| smt_cast_io!(
        "writing get model query" => write!(w, "(get-model)\n")
      )
    )
  }

  /** Parse the result of a get-model. */
  fn parse_get_model<'a>(
    & 'a mut self
  ) -> Res<Vec<(Parser::Ident, Parser::Value)>>
  where Parser: 'a {
    self.parse(
      |bytes, parser| wrap!(
        alt!(
          bytes,
          unexpected |
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
  }

  /** Get-model command. */
  fn get_model(& mut self) -> Res<Vec<(Parser::Ident, Parser::Value)>> {
    try_cast!(
      self.print_get_model()
    ) ;
    self.parse_get_model()
  }

  /** Parse the result of a get-values. */
  fn parse_get_values(
    & mut self, info: & Parser::I
  ) -> Res<Vec<(Parser::Expr, Parser::Value)>> {
    self.parse(
      |bytes, parser| wrap!(
        call!(
          bytes,
          closure!(
            alt!(
              unexpected |
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
    )
  }

  /** Get-assertions command. */
  fn print_get_assertions(& mut self) -> Res<()> {
    self.write(
      |w| smt_cast_io!(
        "writing get assertions query" => write!(w, "(get-assertions)\n")
      )
    )
  }
  /** Get-assignment command. */
  fn print_get_assignment(& mut self) -> Res<()> {
    self.write(
      |w| smt_cast_io!(
        "writing get assignment query" => write!(w, "(get-assignment)\n")
      )
    )
  }
  /** Get-unsat-assumptions command. */
  fn print_get_unsat_assumptions(& mut self) -> Res<()> {
    self.write(
      |w| smt_cast_io!(
        "writing get unsat assumptions query" =>
          write!(w, "(get-unsat-assumptions)\n")
      )
    )
  }
  /** Get-proop command. */
  fn print_get_proof(& mut self) -> Res<()> {
    self.write(
      |w| smt_cast_io!(
        "writing get proof query" =>
          write!(w, "(get-proof)\n")
      )
    )
  }
  /** Get-unsat-core command. */
  fn print_get_unsat_core(& mut self) -> Res<()> {
    self.write(
      |w| smt_cast_io!(
        "writing get unsat core query" =>
          write!(w, "(get-unsat-core)\n")
      )
    )
  }
}

/** Queries with ident printing. */
pub trait QueryIdent<
  'kid, Parser: ParseSmt2 + 'static, Info, Ident: Sym2Smt<Info>
> : Solver<'kid, Parser> + Query<'kid, Parser> {
  /** Check-sat with assumptions command. */
  fn print_check_sat_assuming(
    & mut self, bool_vars: & [ Ident ], info: & Info
  ) -> Res<()> {
    let err_info = "writing check sat assuming query" ;
    match * self.solver().conf.get_check_sat_assuming() {
      Some(ref cmd) => {
        self.write(
          |w| {
            smtry_io!( err_info => write!(w, "({}\n ", cmd) ) ;
            for sym in bool_vars {
              smtry_io!( err_info =>
                write!(w, " ") ;
                sym.sym_to_smt2(w, info)
              )
            } ;
            smt_cast_io!( err_info => write!(w, "\n)\n") )
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

  /** Check-sat assuming command. */
  fn check_sat_assuming(
    & mut self, idents: & [ Ident ], info: & Info
  ) -> Res<bool> {
    try_cast!(
      self.print_check_sat_assuming(idents, info)
    ) ;
    self.parse_check_sat()
  }
}

/** Queries with expr printing. */
pub trait QueryExpr<
  'kid, Parser: ParseSmt2 + 'static, Info, Expr: Expr2Smt<Info>
> : Solver<'kid, Parser> + Query<'kid, Parser> {
  /** Get-values command. */
  fn print_get_values(
    & mut self, exprs: & [ Expr ], info: & Info
  ) -> Res<()> {
    let err_info = "writing get value query" ;
    self.write(
      |w| {
        smtry_io!( err_info => write!(w, "(get-value (") ) ;
        for e in exprs {
          smtry_io!( err_info =>
            write!(w, "\n  ") ;
            e.expr_to_smt2(w, info)
          )
        } ;
        smt_cast_io!( err_info => write!(w, "\n) )\n") )
      }
    )
  }
}

/** Queries with expr printing and related print/parse information. */
pub trait QueryExprInfo<
  'kid, Parser: ParseSmt2 + 'static, Expr: Expr2Smt<Parser::I>
> : Solver<'kid, Parser> + QueryExpr<'kid, Parser, Parser::I, Expr> {
  /** Get-values command. */
  fn get_values(
    & mut self, exprs: & [ Expr ], info: & Parser::I
  ) -> Res<Vec<(Parser::Expr, Parser::Value)>> {
    try_cast!(
      self.print_get_values(exprs, info)
    ) ;
    self.parse_get_values(info)
  }
}
