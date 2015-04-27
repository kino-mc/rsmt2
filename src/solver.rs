#![ doc = "
Implements all the printing and parsing methods for the SMT lib 2 standard.
"]

use std::process::{
  Command, Child, Stdio
} ;
use std::io ;
use std::ffi::OsStr ;
use std::convert::AsRef ;

use ::conf::SolverConf ;
use ::common::* ;
use ::solver_traits::* ;


/// Contains the actual z3 process.
pub struct Solver {
  // /// The command used to run the solver.
  // cmd: Command,
  /// The actual z3 child process.
  kid: Child,
  /// The solver specific information.
  conf: SolverConf,
}

impl Solver {

  /// Creates a new solver from a command and some arguments.
  /// The command that will run is `<cmd> -in <args>`.
  ///
  /// Launches the child process.
  pub fn new< S: AsRef<OsStr> >(
    cmd: S, args: & [ S ]
  ) -> io::Result<Self> {
    // Building the command.
    let mut cmd = Command::new(cmd) ;
    cmd.arg("-in") ;
    cmd.arg("-smt2") ;
    cmd.args(args) ;
    // Setting up pipes for child process.
    cmd.stdin(Stdio::piped()) ;
    cmd.stdout(Stdio::piped()) ;
    cmd.stderr(Stdio::piped()) ;
    // Spawning the child process.
    match cmd.spawn() {
      Ok(kid) => {
        let mut solver = Solver {
          // cmd: cmd,
          kid: kid,
          conf: SolverConf::z3(),
        } ;
        solver.set_option(":print-success", "true").unwrap() ;
        Ok( solver )
      },
      Err(e) => Err( e ),
    }
  }


  /// Creates a new solver usind the default command.
  /// The command that will run is `z3 -in -m`.
  ///
  /// Launches the child process.
  pub fn new_z3() -> io::Result<Self> {
    let args = vec![] ;
    Solver::new("z3", & args)
  }

  /// Returns a pointer to the writer on the stdin of the process.
  fn writer(& mut self) -> & mut io::Write {
    if let Some( ref mut stdin ) = self.kid.stdin {
      stdin
    } else {
      panic!("can't access stdin of child process")
    }
  }

  /// Returns a pointer to the reader on the stdout of the process.
  fn out_reader(& mut self) -> & mut io::Read {
    if let Some( ref mut stdout ) = self.kid.stdout {
      stdout
    } else {
      panic!("can't access stdout of child process")
    }
  }

  /// Returns a pointer to the reader on the stderr of the process.
  fn err_reader(& mut self) -> & mut io::Read {
    if let Some( ref mut stderr ) = self.kid.stderr {
      stderr
    } else {
      panic!("can't access stderr of child process")
    }
  }

  /// Gets the standard error output of the process as a string.
  pub fn out_as_string(& mut self) -> io::Result<String> {
    let mut s = String::new() ;
    match self.out_reader().read_to_string(& mut s) {
      Ok(_) => Ok(s),
      Err(e) => Err(e),
    }
  }

  /// Gets the standard error output of the process as a string.
  pub fn err_as_string(& mut self) -> io::Result<String> {
    let mut s = String::new() ;
    match self.err_reader().read_to_string(& mut s) {
      Ok(_) => Ok(s),
      Err(e) => Err(e),
    }
  }
}

impl Smt2Print for Solver {

  fn comment(
    & mut self, lines: ::std::str::Lines
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    for line in lines { try!( write!(writer, ";; {}\n", line) ) } ;
    write!(writer, "\n")
  }

  // |===| (Re)starting and terminating.

  fn reset(
    & mut self
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(reset)\n\n")
  }
  fn set_logic(
    & mut self, logic: & Logic
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    try!( write!(writer, "(set-logic ") ) ;
    try!( logic.to_smt2(writer) ) ;
    write!(writer, ")\n\n")
  }
  fn set_option(
    & mut self, option: & str, value: & str
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(set-option {} {})\n\n", option, value)
  }
  fn exit(
    & mut self
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(exit)\n")
  }

  // |===| Modifying the assertion stack.

  fn push(
    & mut self, n: & u8
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(push {})\n\n", n)
  }
  fn pop(
    & mut self, n: & u8
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(pop {})\n\n", n)
  }
  fn reset_assertions(
    & mut self
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(reset-assertions)\n\n")
  }

  // |===| Introducing new symbols.

  fn declare_sort<Sort: Printable>(
    & mut self, sort: Sort, arity: & u8
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    try!( write!(writer, "(declare-sort ") ) ;
    try!( sort.to_smt2(writer) ) ;
    write!(writer, " {})\n\n", arity)
  }
  fn define_sort<Sort: Printable, Expr: Printable>(
    & mut self, sort: Sort, args: & [ Expr ], body: Expr
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    try!( write!(writer, "( define-sort ") ) ;
    try!( sort.to_smt2(writer) ) ;
    try!( write!(writer, "\n   ( ") ) ;
    for arg in args {
      try!( arg.to_smt2(writer) ) ;
      try!( write!(writer, " ") )
    } ;
    try!( write!(writer, ")\n   ") ) ;
    try!( body.to_smt2(writer) ) ;
    write!(writer, "\n)\n\n")
  }
  fn declare_fun<Sort: Printable, Ident: Printable>(
    & mut self, symbol: Ident, args: & [ Sort ], out: Sort
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    try!( write!(writer, "(declare-fun ") ) ;
    try!( symbol.to_smt2(writer) ) ;
    try!( write!(writer, " ( ") ) ;
    for arg in args {
      try!( arg.to_smt2(writer) ) ;
      try!( write!(writer, " ") )
    } ;
    try!( write!(writer, ") ") ) ;
    try!( out.to_smt2(writer) ) ;
    write!(writer, ")\n\n")
  }
  fn declare_const<Sort: Printable, Ident: Printable>(
    & mut self, symbol: Ident, out_sort: Sort
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    try!( write!(writer, "(declare-const ") ) ;
    try!( symbol.to_smt2(writer) ) ;
    try!( write!(writer, " ") ) ;
    try!( out_sort.to_smt2(writer) ) ;
    write!(writer, ")\n\n")
  }
  fn define_fun<Sort: Printable, Ident: Printable, Expr: Printable>(
    & mut self,
    symbol: Ident, args: & [ (Ident, Sort) ], out: Sort, body: Expr
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    try!( write!(writer, "(define-fun ") ) ;
    try!( symbol.to_smt2(writer) ) ;
    try!( write!(writer, " ( ") ) ;
    for arg in args {
      let (ref id, ref sort) = * arg ;
      try!( write!(writer, "(") ) ;
      try!( id.to_smt2(writer) ) ;
      try!( write!(writer, " ") ) ;
      try!( sort.to_smt2(writer) ) ;
      try!( write!(writer, ") ") )
    } ;
    try!( write!(writer, ") ") ) ;
    try!( out.to_smt2(writer) ) ;
    try!( write!(writer, "\n   ") ) ;
    try!( body.to_smt2(writer) ) ;
    write!(writer, "\n)\n\n")
  }
  fn define_funs_rec<Sort: Printable, Ident: Printable, Expr: Printable>(
    & mut self,
    funs: & [ (Ident, & [ (Ident, Sort) ], Sort, Expr) ]
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    // Header.
    try!( write!(writer, "(define-funs-rec (\n") ) ;

    // Signatures.
    for fun in funs {
      let (ref id, ref args, ref out, _) = * fun ;
      try!( write!(writer, "   (") ) ;
      try!( id.to_smt2(writer) ) ;
      try!( write!(writer, " ( ") ) ;
      for arg in * args {
        let (ref arg, ref sort) = * arg ;
        try!( write!(writer, "(") ) ;
        try!( arg.to_smt2(writer) ) ;
        try!( write!(writer, " ") ) ;
        try!( sort.to_smt2(writer) ) ;
        try!( write!(writer, ") ") ) ;
      } ;
      try!( write!(writer, ") ") ) ;
      try!( out.to_smt2(writer) ) ;
      try!( write!(writer, ")\n") )
    } ;
    try!( write!(writer, " ) (") ) ;

    // Bodies
    for fun in funs {
      let (_, _, _, ref body) = * fun ;
      try!( write!(writer, "\n   ") ) ;
      try!( body.to_smt2(writer) )
    } ;
    write!(writer, "\n )\n)\n\n")
  }
  fn define_fun_rec<Sort: Printable, Ident: Printable, Expr: Printable>(
    & mut self,
    symbol: Ident, args: & [ (Ident, Sort) ], out: Sort, body: Expr
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    // Header.
    try!( write!(writer, "(define-fun-rec (\n") ) ;

    // Signature.
    try!( write!(writer, "   (") ) ;
    try!( symbol.to_smt2(writer) ) ;
    try!( write!(writer, " ( ") ) ;
    for arg in args {
      let (ref arg, ref sort) = * arg ;
      try!( write!(writer, "(") ) ;
      try!( arg.to_smt2(writer) ) ;
      try!( write!(writer, " ") ) ;
      try!( sort.to_smt2(writer) ) ;
      try!( write!(writer, ") ") ) ;
    } ;
    try!( write!(writer, ") ") ) ;
    try!( out.to_smt2(writer) ) ;
    try!( write!(writer, ")\n") ) ;
    try!( write!(writer, " ) (") ) ;

    // Body.
    try!( write!(writer, "\n   ") ) ;
    try!( body.to_smt2(writer) ) ;
    write!(writer, "\n )\n)\n\n")
  }

  // |===| Asserting and inspecting formulas.

  fn assert<Expr: Printable>(
    & mut self, expr: Expr
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    try!( write!(writer, "(assert\n  ") ) ;
    try!( expr.to_smt2(writer) ) ;
    write!(writer, "\n)")
  }
  fn get_assertions(
    & mut self
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(get-assertions)\n\n")
  }

  // |===| Checking for satisfiability.

  fn check_sat(
    & mut self
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(check-sat)\n\n")
  }
  fn check_sat_assuming<Ident: Printable>(
    & mut self, bool_vars: & [ Ident ]
  ) -> IoResUnit {
    let cmd = self.conf.check_sat_assuming ;
    let mut writer = self.writer() ;
    try!( write!(writer, "({}\n ", cmd) );
    for v in bool_vars {
      try!( write!(writer, " ") ) ;
      try!( v.to_smt2(writer) )
    } ;
    write!(writer, "\n)\n\n")
  }

  // |===| Inspecting models.

  fn get_value<Expr: Printable>(
    & mut self, exprs: & [ Expr ]
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    try!( write!(writer, "(get-value") ) ;
    for e in exprs {
      try!( write!(writer, "\n  ") ) ;
      try!( e.to_smt2(writer) )
    } ;
    write!(writer, "\n)\n\n")
  }
  fn get_assignment(
    & mut self
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(get-assignment)\n\n")
  }
  fn get_model(
    & mut self
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(get-model)\n\n")
  }

  // |===| Inspecting proofs.

  fn get_unsat_assumptions(
    & mut self
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(get-unsat-assumptions)\n\n")
  }
  fn get_proof(
    & mut self
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(get-proof)\n\n")
  }
  fn get_unsat_core(
    & mut self
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(get-unsat-core)\n\n")
  }

  // |===| Inspecting settings.

  fn get_info(
    & mut self, flag: & str
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(get-info {})\n\n", flag)
  }
  fn get_option(
    & mut self, option: & str
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(get-option {})\n\n", option)
  }

  // |===| Script information.

  fn set_info(
    & mut self, attribute: & str
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(set-info {})\n\n", attribute)
  }
  fn echo(
    & mut self, text: & str
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(echo \"{}\")\n\n", text)
  }
}


/// Can parse the result of SMT lib 2 queries.
impl<
  Ident, Value, Expr, Proof
> Smt2Parse<Ident, Value, Expr, Proof> for Solver {

  fn parse_success(& mut self) -> IoResUnit {
    Ok(())
  }

  fn parse_assertions(& mut self) -> IoRes<Option<Vec<Expr>>> {
    Ok(None)
  }

  fn parse_check_sat(& mut self) -> IoResBool {
    Ok(false)
  }

  fn parse_value(& mut self) -> IoRes<Option<Vec<Value>>> {
    Ok(None)
  }
  fn parse_assignment(& mut self) -> IoRes<Option<Vec<(Ident, Value)>>> {
    Ok(None)
  }
  fn parse_model(& mut self) -> IoRes<Option<Vec<(Ident, Value)>>> {
    Ok(None)
  }

  fn parse_unsat_assumptions(& mut self) -> IoRes<Option<Vec<Ident>>> {
    Ok(None)
  }
  fn parse_proof(& mut self) -> IoRes<Option<Proof>> {
    Ok(None)
  }
  fn parse_unsat_core(& mut self) -> IoRes<Option<Vec<Ident>>> {
    Ok(None)
  }

  fn parse_info(& mut self) -> IoRes<Option<String>> {
    Ok(None)
  }
  fn parse_option(& mut self) -> IoRes<Option<String>> {
    Ok(None)
  }

}

impl<
  Ident: Printable,
  Value,
  Sort: Printable,
  Expr: Printable,
  Proof,
> Smt2GetNow<Ident, Value, Sort, Expr, Proof> for Solver {}

impl<
  Ident: Printable,
  Value,
  Sort: Printable,
  Expr: Printable,
  Proof,
> Smt2Solver<Ident, Value, Sort, Expr, Proof> for Solver {}


