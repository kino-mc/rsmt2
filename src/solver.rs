#![ doc = "
Implements all the printing and parsing methods for the SMT lib 2 standard.
"]

use std::process::{
  Command, Child, Stdio
} ;
use std::io ;
use std::ffi::OsStr ;
use std::convert::AsRef ;


/// Contains the actual z3 process.
pub struct Solver {
  /// The command used to run the solver.
  cmd: Command,
  /// The actual z3 child process.
  kid: Child,
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
    cmd.args(args) ;
    // Setting up pipes for child process.
    cmd.stdin(Stdio::piped()) ;
    cmd.stdout(Stdio::piped()) ;
    cmd.stderr(Stdio::piped()) ;
    // Spawning the child process.
    match cmd.spawn() {
      Ok(kid) => Ok(
        Solver {
          cmd: cmd, kid: kid,
        }
      ),
      Err(e) => Err( e ),
    }
  }


  /// Creates a new solver usind the default command.
  /// The command that will run is `z3 -in -m`.
  ///
  /// Launches the child process.
  pub fn new_default() -> io::Result<Self> {
    let args = vec!["-m"] ;
    Solver::new("z3", & args)
  }

  /// Returns a pointer to the writer on the stdin of the process.
  fn in_writer(& mut self) -> & mut io::Write {
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
  pub fn err_as_string(& mut self) -> io::Result<String> {
    let mut s = String::new() ;
    match self.err_reader().read_to_string(& mut s) {
      Ok(_) => Ok(s),
      Err(e) => Err(e),
    }
  }

}