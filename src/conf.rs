//! Solver configuration, contains backend-solver-specific info.
//!
//! Do **NOT** use wildcards when matching over `SmtStyle`. We want the code to
//! fail to compile whenever we add a solver. Likewise, do not use `if let`
//! with `SmtStyle`.

use std::fmt ;

use { SmtRes, Solver } ;

use self::SmtStyle::* ;

/// A configuration item is either a keyword or unsupported.
pub type ConfItem = Option<& 'static str> ;

/// Value of an unsupported configuration item.
#[inline]
fn unsupported() -> ConfItem { None }
/// Keyword for a configuration item.
#[inline]
fn supported(keyword: & 'static str) -> ConfItem { Some(keyword) }


/// Solver styles.
#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
pub enum SmtStyle {
  /// Z3-style smt solver.
  Z3,
  /// CVC4-style smt solver.
  ///
  /// **NB**: CVC4 hasn't been properly tested yet.
  CVC4,
}

impl SmtStyle {
  /// Default configuration for a solver style.
  pub fn default(self) -> SmtConf {
    let cmd = self.cmd() ;
    match self {
      Z3 => SmtConf {
        style: self,
        cmd: cmd,
        options: vec![
          "-in".into(), "-smt2".into()
        ],
        models: true,
        incremental: true,
        parse_success: false,
        unsat_cores: false,
        check_sat_assuming: supported("check-sat"),
      },
      CVC4 => SmtConf {
        style: self,
        cmd: cmd,
        options: vec![
          "-q".into(), "--interactive".into(),
          "--lang".into(), "smt2".into(),
        ],
        models: false,
        incremental: false,
        parse_success: false,
        unsat_cores: false,
        check_sat_assuming: unsupported(),
      },
    }
  }

  /// A solver style from a string.
  #[allow(dead_code)]
  pub fn of_str(s: & str) -> Option<Self> {
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
      Z3 => "z3".to_string(),
      CVC4 => "cvc4".to_string(),
    }
  }
  /// Default command for a solver style.
  #[cfg( windows )]
  pub fn cmd(& self) -> String {
    match * self {
      Z3 => "z3.exe".to_string(),
      CVC4 => "cvc4.exe".to_string(),
    }
  }
}

impl fmt::Display for SmtStyle {
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
  style: SmtStyle,
  /// Solver command.
  cmd: String,
  /// Options to call the solver with.
  options: Vec<String>,
  /// Model production.
  models: bool,
  /// Incrementality.
  incremental: bool,
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

  /// Creates a new cvc4-like solver configuration.
  ///
  /// # Examples
  ///
  /// ```
  /// # use rsmt2::SmtConf ;
  /// let conf = SmtConf::cvc4() ;
  /// assert! {
  ///   conf.get_cmd() == "cvc4" || conf.get_cmd() == "cvc4.exe"
  /// }
  /// ```
  #[inline]
  pub fn cvc4() -> Self { CVC4.default() }


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

  /// Model production.
  pub fn get_models(& self) -> bool {
    self.models
  }
  /// Activates model production.
  pub fn models(& mut self) {
    if self.models {
      return ()
    } else {
      self.models = true
    }
    match self.style {
      CVC4 => self.options.push( "--produce-models".into() ),
      Z3 => (),
    }
  }

  /// Incrementality.
  pub fn get_incremental(& self) -> bool {
    self.incremental
  }
  /// Activates incrementality (push/pop, check-sat-assuming).
  pub fn incremental(& mut self) {
    if self.incremental {
      return ()
    } else {
      self.incremental = true
    }
    match self.style {
      CVC4 => self.options.push( "--incremental".into() ),
      Z3 => (),
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
  pub fn get_options(& self) -> & [ String ] { & self.options }

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
  pub fn option<S: Into<String>>(& mut self, o: S) -> & mut Self {
    self.options.push( o.into() ) ;
    self
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
  pub fn cmd<S: Into<String>>(& mut self, cmd: S) -> & mut Self {
    let cmd = cmd.into() ;
    let mut iter = cmd.split(" ") ;

    'set_cmd: while let Some(cmd) = iter.next() {
      if ! cmd.is_empty() {
        self.cmd = cmd.into() ;
        break 'set_cmd
      }
    }

    for option in iter {
      if ! option.is_empty() {
        self.options.push( option.into() )
      }
    }

    self
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