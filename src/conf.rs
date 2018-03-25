//! Solver configuration, contains backend-solver-specific info.

use std::fmt ;

use { SmtRes, Solver } ;

use self::SolverStyle::* ;

/// A configuration item is either a keyword or unsupported.
pub type ConfItem = Option<& 'static str> ;

/// Value of an unsupported configuration item.
#[inline]
fn unsupported() -> ConfItem { None }
/// Keyword for a configuration item.
#[inline]
fn supported(keyword: & 'static str) -> ConfItem { Some(keyword) }


/// Solver styles.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum SolverStyle {
  /// Z3-style smt solver.
  Z3,
  /// CVC4-style smt solver.
  ///
  /// **NB**: CVC4 hasn't been properly tested yet.
  CVC4,
}

impl SolverStyle {
  /// Default configuration for a solver style.
  pub fn default(self) -> SmtConf {
    let cmd = self.cmd() ;
    match self {
      Z3 => SmtConf {
        style: self,
        cmd: cmd,
        options: vec![
          "-in", "-smt2"
        ],
        parse_success: false,
        unsat_cores: false,
        check_sat_assuming: supported("check-sat"),
      },
      CVC4 => SmtConf {
        style: self,
        cmd: cmd,
        options: vec![
          "--smtlib-strict", "-qqqqq", "--interactive"
        ],
        parse_success: false,
        unsat_cores: false,
        check_sat_assuming: unsupported(),
      },
    }
  }
  /// A solver style from a string.
  #[allow(dead_code)]
  pub fn of_str(s: & str) -> Option<SolverStyle> {
    match s {
      "z3" | "Z3" => Some(Z3),
      "cvc4" | "CVC4" => Some(CVC4),
      _ => None,
    }
  }
  /// Legal string representations of solver styles.
  #[allow(dead_code)]
  pub fn str_keys() -> Vec<& 'static str> {
    vec![ "z3", "Z3", "cvc4", "CVC4" ]
  }

  /// Default command for a solver style.
  #[cfg( not(windows) )]
  pub fn cmd(& self) -> String {
    match * self {
      Z3 => "z3".to_string(), CVC4 => "cvc4".to_string(),
    }
  }
  /// Default command for a solver style.
  #[cfg( windows )]
  pub fn cmd(& self) -> String {
    match * self {
      Z3 => "z3.exe".to_string(), CVC4 => "cvc4.exe".to_string(),
    }
  }
}

impl fmt::Display for SolverStyle {
  fn fmt(& self, fmt: & mut fmt::Formatter) -> fmt::Result {
    match * self {
      Z3 => write!(fmt, "z3"),
      CVC4 => write!(fmt, "cvc4"),
    }
  }
}


/// Configuration and solver specific info.
#[derive(Debug, Clone)]
pub struct SmtConf {
  /// Solver style.
  style: SolverStyle,
  /// Solver command.
  cmd: String,
  /// Options to call the solver with.
  options: Vec<& 'static str>,
  /// Parse success.
  parse_success: bool,
  /// Triggers unsat-core production.
  unsat_cores: bool,
  /// Keyword for check-sat with assumptions.
  check_sat_assuming: ConfItem,
}

impl SmtConf {
  /// Creates a new z3-like solver configuration.
  ///
  /// # Examples
  ///
  /// ```
  /// # use rsmt2::SmtConf ;
  /// let conf = SmtConf::z3() ;
  /// assert! {
  ///   conf.get_cmd() == "z3" || conf.get_cmd() == "z3.exe"
  /// }
  /// ```
  #[inline]
  pub fn z3() -> Self { Z3.default() }


  /// Spawns the solver.
  ///
  /// # Examples
  ///
  /// ```
  /// # use rsmt2::SmtConf ;
  /// let _solver = SmtConf::z3().spawn(()).unwrap() ;
  /// ```
  #[inline]
  pub fn spawn<Parser>(self, parser: Parser) -> SmtRes<Solver<Parser>> {
    Solver::new(self, parser)
  }

  /// Concise description of the underlying solver.
  ///
  /// # Examples
  ///
  /// ```
  /// # use rsmt2::SmtConf ;
  /// assert_eq! { SmtConf::z3().desc(), "z3" }
  /// ```
  #[inline]
  pub fn desc(& self) -> & str {
    match self.style {
      Z3 => "z3",
      CVC4 => "cvc4",
    }
  }

  /// Solver command.
  ///
  /// # Examples
  ///
  /// ```
  /// # use rsmt2::SmtConf ;
  /// let conf = SmtConf::z3() ;
  /// assert! {
  ///   conf.get_cmd() == "z3" || conf.get_cmd() == "z3.exe"
  /// }
  /// ```
  #[inline]
  pub fn get_cmd(& self) -> & str { & self.cmd }

  /// Options of the configuration.
  ///
  /// # Examples
  ///
  /// ```
  /// # use rsmt2::SmtConf ;
  /// assert_eq! {
  ///   SmtConf::z3().get_options(), & [ "-in", "-smt2" ]
  /// }
  /// ```
  #[inline]
  pub fn get_options(& self) -> & [& 'static str] { & self.options }

  /// Indicates if print success is active.
  ///
  /// # Examples
  ///
  /// ```
  /// # use rsmt2::SmtConf ;
  /// assert! { ! SmtConf::z3().get_print_success() }
  /// ```
  #[inline]
  pub fn get_print_success(& self) -> bool { self.parse_success }

  /// Indicates if unsat cores is active.
  ///
  /// # Examples
  ///
  /// ```
  /// # use rsmt2::SmtConf ;
  /// assert! { ! SmtConf::z3().get_unsat_cores() }
  /// ```
  #[inline]
  pub fn get_unsat_cores(& self) -> bool { self.unsat_cores }

  /// Keyword for check-sat with assumptions.
  ///
  /// # Examples
  ///
  /// ```
  /// # use rsmt2::SmtConf ;
  /// assert_eq! {
  ///   SmtConf::z3().get_check_sat_assuming(), Some("check-sat")
  /// }
  /// ```
  #[inline]
  pub fn get_check_sat_assuming(& self) -> ConfItem {
    self.check_sat_assuming.as_ref().map( |s| * s )
  }

  /// Adds an option to the configuration.
  ///
  /// # Examples
  ///
  /// ```
  /// # use rsmt2::SmtConf ;
  /// let mut conf = SmtConf::z3() ;
  /// conf.option("arith.euclidean_solver=true") ;
  /// assert_eq! {
  ///   conf.get_options(),
  ///   & [ "-in", "-smt2", "arith.euclidean_solver=true" ]
  /// }
  /// ```
  #[inline]
  pub fn option(& mut self, o: & 'static str) {
    self.options.push(o)
  }

  /// Sets the command for the solver.
  ///
  /// # Examples
  ///
  /// ```
  /// # use rsmt2::SmtConf ;
  /// let mut conf = SmtConf::z3() ;
  /// conf.cmd("my_custom_z3_command") ;
  /// assert_eq! { conf.get_cmd(), "my_custom_z3_command" }
  /// ```
  #[inline]
  pub fn cmd<S: Into<String>>(& mut self, cmd: S) {
    self.cmd = cmd.into()
  }

  /// Activates parse sucess.
  ///
  /// # Examples
  ///
  /// ```
  /// # use rsmt2::SmtConf ;
  /// let mut conf = SmtConf::z3() ;
  /// conf.print_success() ;
  /// assert! { conf.get_print_success() }
  /// ```
  #[inline]
  #[cfg(not(no_parse_success))]
  pub fn print_success(& mut self) {
    self.parse_success = true
  }

  /// Activates unsat-core production.
  ///
  /// # Examples
  ///
  /// ```
  /// # use rsmt2::SmtConf ;
  /// let mut conf = SmtConf::z3() ;
  /// conf.unsat_cores() ;
  /// assert! { conf.get_unsat_cores() }
  /// ```
  #[inline]
  pub fn unsat_cores(& mut self) {
    self.unsat_cores = true
  }
}