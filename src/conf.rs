//! Solver configuration, contains backend-solver-specific info.
//!
//! Do **NOT** use wildcards when matching over `SmtStyle`. We want the code to fail to compile
//! whenever we add a solver. Likewise, do not use `if let` with `SmtStyle`.
//!
//! Note that the command for each solver can be passed through environment variables, see
//! - [`Z3_ENV_VAR`],
//! - [`CVC4_ENV_VAR`],
//! - [`YICES_2_ENV_VAR`], and
//! - the [`SmtConf::z3_or_env`], [`SmtConf::cvc4_or_env`], and [`SmtConf::yices_2_or_env`]
//!   constructors.

use std::fmt;

use crate::{SmtRes, Solver};

use self::SmtStyle::*;

/// A configuration item is either a keyword or unsupported.
pub type ConfItem = Option<&'static str>;

/// Value of an unsupported configuration item.
#[inline]
fn unsupported() -> ConfItem {
    None
}
/// Keyword for a configuration item.
#[inline]
fn supported(keyword: &'static str) -> ConfItem {
    Some(keyword)
}

/// Environment variable providing the command for z3.
pub const Z3_ENV_VAR: &str = "RSMT2_Z3_CMD";
/// Environment variable providing the command for CVC4.
pub const CVC4_ENV_VAR: &str = "RSMT2_CVC4_CMD";
/// Environment variable providing the command for Yices 2.
pub const YICES_2_ENV_VAR: &str = "RSMT2_YICES_2_CMD";

/// Retrieves the value of an environment variable.
fn get_env_var(env_var: &str) -> SmtRes<Option<String>> {
    match std::env::var(env_var) {
        Ok(res) => Ok(Some(res)),
        Err(std::env::VarError::NotPresent) => Ok(None),
        Err(std::env::VarError::NotUnicode(cmd)) => bail!(
            "value of environment variable `{}` is not legal unicode: `{}`",
            env_var,
            cmd.to_string_lossy(),
        ),
    }
}

/// Solver styles.
///
/// - [z3][z3]: full support
/// - [cvc4][cvc4]: full support in theory, but only partially tested. Note that `get-value` is
///   known to crash some versions of CVC4.
/// - [yices 2][yices 2]: full support in theory, but only partially tested. Command `get-model`
///   will only work on Yices 2 > `2.6.1`, and needs to be activated in [`SmtConf`] with
///   [`SmtConf::models`]. To understand why, see <https://github.com/SRI-CSL/yices2/issues/162>.
///   
/// [z3]: https://github.com/Z3Prover/z3 (z3 github repository)
/// [cvc4]: https://cvc4.github.io/ (cvc4 github pages)
/// [yices 2]: https://yices.csl.sri.com/ (yices 2 official page)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
pub enum SmtStyle {
    /// Z3-style smt solver.
    Z3,
    /// CVC4-style smt solver.
    ///
    /// **NB**: CVC4 has only been partially tested at this point.
    CVC4,
    /// Yices-2-style smt solver.
    ///
    /// **NB**: Yices 2 has only been partially tested at this point.
    Yices2,
}

impl SmtStyle {
    /// Configuration constructor.
    pub fn new(self, cmd: impl Into<String>) -> SmtConf {
        let cmd = cmd.into();
        match self {
            Z3 => SmtConf {
                style: self,
                cmd,
                options: vec!["-in".into(), "-smt2".into()],
                models: true,
                incremental: true,
                parse_success: false,
                unsat_cores: false,
                interpolants: true,
                check_sat_assuming: supported("check-sat-assuming"),
            },
            CVC4 => SmtConf {
                style: self,
                cmd,
                options: vec![
                    "-q".into(),
                    "--no-interactive".into(),
                    "--lang".into(),
                    "smt2".into(),
                ],
                models: false,
                incremental: false,
                parse_success: false,
                unsat_cores: false,
                interpolants: false,
                check_sat_assuming: unsupported(),
            },
            Yices2 => SmtConf {
                style: self,
                cmd,
                options: vec![],
                models: false,
                incremental: false,
                parse_success: false,
                unsat_cores: false,
                interpolants: false,
                check_sat_assuming: supported("check-sat-assuming"),
            },
        }
    }

    /// Default configuration for a solver style.
    ///
    /// # Warning
    ///
    /// The command used to run a particular solver is up to the end-user. As such, it **does not
    /// make sense** to use default commands for anything else than local testing. You should
    /// explicitely pass the command to use with [`Self::new`] instead.
    pub fn default(self) -> SmtConf {
        self.new(self.cmd())
    }

    /// A solver style from a string.
    #[allow(dead_code)]
    pub fn of_str(s: &str) -> Option<Self> {
        match s {
            "z3" | "Z3" => Some(Z3),
            "cvc4" | "CVC4" => Some(CVC4),
            "Yices2" | "yices2" | "YICES2" | "Yices 2" | "yices 2" | "YICES 2" => Some(Yices2),
            _ => None,
        }
    }
    /// Legal string representations of solver styles.
    #[allow(dead_code)]
    pub fn str_keys() -> Vec<&'static str> {
        vec![
            "z3", "Z3", "cvc4", "CVC4", "Yices2", "yices2", "YICES2", "Yices 2", "yices 2",
            "YICES 2",
        ]
    }

    /// Solver style command from the corresponding environment variable.
    ///
    /// The environement variables scanned are [`Z3_ENV_VAR`], [`CVC4_ENV_VAR`] and
    /// [`YICES_2_ENV_VAR`].
    pub fn env_cmd(self) -> SmtRes<Option<String>> {
        match self {
            Z3 => get_env_var(Z3_ENV_VAR),
            CVC4 => get_env_var(CVC4_ENV_VAR),
            Yices2 => get_env_var(YICES_2_ENV_VAR),
        }
    }

    /// Default command for a solver style.
    #[cfg(not(windows))]
    pub fn cmd(self) -> &'static str {
        match self {
            Z3 => "z3",
            CVC4 => "cvc4",
            Yices2 => "yices",
        }
    }
    /// Default command for a solver style.
    #[cfg(windows)]
    pub fn cmd(self) -> &'static str {
        match self {
            Z3 => "z3.exe",
            CVC4 => "cvc4.exe",
            Yices2 => "yices.exe",
        }
    }

    /// True if `self` is [`Self::Z3`].
    pub fn is_z3(self) -> bool {
        self == Self::Z3
    }
}

impl fmt::Display for SmtStyle {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Z3 => write!(fmt, "z3"),
            CVC4 => write!(fmt, "cvc4"),
            Yices2 => write!(fmt, "yices2"),
        }
    }
}

/// Configuration and solver specific info.
///
/// - [z3]: full support
/// - [cvc4]: full support in theory, but only partially tested. Note that `get-value` is
///   known to crash some versions of CVC4.
/// - [yices 2]: full support in theory, but only partially tested. Command `get-model`
///   will only work on Yices 2 > `2.6.1`, and needs to be activated with [`Self::models`]. To
///   understand why, see <https://github.com/SRI-CSL/yices2/issues/162>.
///   
/// [z3]: https://github.com/Z3Prover/z3 (z3 github repository)
/// [cvc4]: https://cvc4.github.io/ (cvc4 github pages)
/// [yices 2]: https://yices.csl.sri.com/ (yices 2 official page)
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
    /// Triggers interpolant production.
    interpolants: bool,
    /// Keyword for check-sat with assumptions.
    check_sat_assuming: ConfItem,
}

impl SmtConf {
    /// Solver style accessor.
    pub fn style(&self) -> SmtStyle {
        self.style
    }

    /// Creates a new z3-like solver configuration.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// let conf = SmtConf::z3("my_z3_command");
    /// assert!(conf.get_cmd() == "my_z3_command")
    /// ```
    #[inline]
    pub fn z3(cmd: impl Into<String>) -> Self {
        Z3.new(cmd)
    }

    /// Creates a new cvc4-like solver configuration.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// let conf = SmtConf::cvc4("my_cvc4_command");
    /// assert!(conf.get_cmd() == "my_cvc4_command")
    /// ```
    #[inline]
    pub fn cvc4(cmd: impl Into<String>) -> Self {
        CVC4.new(cmd)
    }

    /// Creates a new yices-2-like solver configuration.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// let conf = SmtConf::yices_2("my_yices_2_command");
    /// assert!(conf.get_cmd() == "my_yices_2_command")
    /// ```
    #[inline]
    pub fn yices_2(cmd: impl Into<String>) -> Self {
        Yices2.new(cmd)
    }

    /// Creates a z3-like solver configuration from an optional, or the value of the [`Z3_ENV_VAR`]
    /// environment variable.
    ///
    /// Fails if `cmd.is_none()` and [`Z3_ENV_VAR`] is not set.
    ///
    /// ```rust
    /// use rsmt2::conf::{SmtConf, Z3_ENV_VAR};
    /// use std::env::{set_var, var_os};
    ///
    /// // Passes the command directly.
    /// let cmd = "z3_explicit";
    /// let explicit_cmd = SmtConf::z3_or_env(Some(cmd.into())).expect("explicit");
    /// assert_eq!(explicit_cmd.get_cmd(), cmd);
    ///
    /// // Error if no command + environment variable not set.
    /// assert_eq!(var_os(Z3_ENV_VAR), None);
    /// let error = SmtConf::z3_or_env(None);
    /// match error {
    ///     Ok(_) => panic!("expected error, got an SMT style"),
    ///     Err(e) => assert_eq!(
    ///         &e.to_string(),
    ///         "no command for z3 provided, \
    ///         and `RSMT2_Z3_CMD` environment variable not set; \
    ///         cannot spawn z3 solver"
    ///     ),
    /// }
    ///
    /// // Retrieves the command from the environment.
    /// let cmd = "z3_implicit";
    /// assert_eq!(Z3_ENV_VAR, "RSMT2_Z3_CMD");
    /// set_var(Z3_ENV_VAR, cmd);
    /// let implicit_cmd = SmtConf::z3_or_env(None).expect("implicit");
    /// assert_eq!(implicit_cmd.get_cmd(), cmd);
    /// ```
    #[inline]
    pub fn z3_or_env(cmd: Option<String>) -> SmtRes<Self> {
        if let Some(cmd) = cmd {
            Ok(Self::z3(cmd))
        } else {
            let cmd = SmtStyle::Z3.env_cmd()?;
            if let Some(cmd) = cmd {
                Ok(Self::z3(cmd))
            } else {
                bail!(
                    "no command for z3 provided, \
                    and `{}` environment variable not set; cannot spawn z3 solver",
                    Z3_ENV_VAR,
                )
            }
        }
    }

    /// Creates a CVC4-like solver configuration from an optional, or the value of the
    /// [`CVC4_ENV_VAR`] environment variable.
    ///
    /// Fails if `cmd.is_none()` and [`CVC4_ENV_VAR`] is not set.
    ///
    /// ```rust
    /// use rsmt2::conf::{SmtConf, CVC4_ENV_VAR};
    /// use std::env::{set_var, var_os};
    ///
    /// // Passes the command directly.
    /// let cmd = "cvc4_explicit";
    /// let explicit_cmd = SmtConf::cvc4_or_env(Some(cmd.into())).expect("explicit");
    /// assert_eq!(explicit_cmd.get_cmd(), cmd);
    ///
    /// // Error if no command + environment variable not set.
    /// assert_eq!(var_os(CVC4_ENV_VAR), None);
    /// let error = SmtConf::cvc4_or_env(None);
    /// match error {
    ///     Ok(_) => panic!("expected error, got an SMT style"),
    ///     Err(e) => assert_eq!(
    ///         &e.to_string(),
    ///         "no command for CVC4 provided, \
    ///         and `RSMT2_CVC4_CMD` environment variable not set; \
    ///         cannot spawn CVC4 solver"
    ///     ),
    /// }
    ///
    /// // Retrieves the command from the environment.
    /// let cmd = "cvc4_implicit";
    /// assert_eq!(CVC4_ENV_VAR, "RSMT2_CVC4_CMD");
    /// set_var(CVC4_ENV_VAR, cmd);
    /// let implicit_cmd = SmtConf::cvc4_or_env(None).expect("implicit");
    /// assert_eq!(implicit_cmd.get_cmd(), cmd);
    /// ```
    #[inline]
    pub fn cvc4_or_env(cmd: Option<String>) -> SmtRes<Self> {
        if let Some(cmd) = cmd {
            Ok(Self::cvc4(cmd))
        } else {
            let cmd = SmtStyle::CVC4.env_cmd()?;
            if let Some(cmd) = cmd {
                Ok(Self::cvc4(cmd))
            } else {
                bail!(
                    "no command for CVC4 provided, \
                    and `{}` environment variable not set; cannot spawn CVC4 solver",
                    CVC4_ENV_VAR,
                )
            }
        }
    }

    /// Creates a Yices-2-like solver configuration from an optional, or the value of the
    /// [`YICES_2_ENV_VAR`] environment variable.
    ///
    /// Fails if `cmd.is_none()` and [`YICES_2_ENV_VAR`] is not set.
    ///
    /// ```rust
    /// use rsmt2::conf::{SmtConf, YICES_2_ENV_VAR};
    /// use std::env::{set_var, var_os};
    ///
    /// // Passes the command directly.
    /// let cmd = "yices_2_explicit";
    /// let explicit_cmd = SmtConf::yices_2_or_env(Some(cmd.into())).expect("explicit");
    /// assert_eq!(explicit_cmd.get_cmd(), cmd);
    ///
    /// // Error if no command + environment variable not set.
    /// assert_eq!(var_os(YICES_2_ENV_VAR), None);
    /// let error = SmtConf::yices_2_or_env(None);
    /// match error {
    ///     Ok(_) => panic!("expected error, got an SMT style"),
    ///     Err(e) => assert_eq!(
    ///         &e.to_string(),
    ///         "no command for Yices 2 provided, \
    ///         and `RSMT2_YICES_2_CMD` environment variable not set; \
    ///         cannot spawn Yices 2 solver"
    ///     ),
    /// }
    ///
    /// // Retrieves the command from the environment.
    /// let cmd = "yices_2_implicit";
    /// assert_eq!(YICES_2_ENV_VAR, "RSMT2_YICES_2_CMD");
    /// set_var(YICES_2_ENV_VAR, cmd);
    /// let implicit_cmd = SmtConf::yices_2_or_env(None).expect("implicit");
    /// assert_eq!(implicit_cmd.get_cmd(), cmd);
    /// ```
    #[inline]
    pub fn yices_2_or_env(cmd: Option<String>) -> SmtRes<Self> {
        if let Some(cmd) = cmd {
            Ok(Self::yices_2(cmd))
        } else {
            let cmd = SmtStyle::Yices2.env_cmd()?;
            if let Some(cmd) = cmd {
                Ok(Self::yices_2(cmd))
            } else {
                bail!(
                    "no command for Yices 2 provided, \
                    and `{}` environment variable not set; cannot spawn Yices 2 solver",
                    YICES_2_ENV_VAR,
                )
            }
        }
    }

    /// Creates a new z3-like solver configuration and command.
    ///
    /// # Warning
    ///
    /// The command used to run a particular solver is up to the end-user. As such, it **does not
    /// make sense** to use default commands for anything else than local testing. You should
    /// explicitely pass the command to use with [`Self::z3`] instead.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// let conf = SmtConf::default_z3();
    /// assert! {
    ///     conf.get_cmd() == "z3" || conf.get_cmd() == "z3.exe"
    /// }
    /// ```
    #[inline]
    pub fn default_z3() -> Self {
        Z3.default()
    }

    /// Creates a new cvc4-like solver configuration and command.
    ///
    /// # Warning
    ///
    /// The command used to run a particular solver is up to the end-user. As such, it **does not
    /// make sense** to use default commands for anything else than local testing. You should
    /// explicitely pass the command to use with [`Self::cvc4`] instead.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// let conf = SmtConf::default_cvc4();
    /// assert! {
    ///     conf.get_cmd() == "cvc4" || conf.get_cmd() == "cvc4.exe"
    /// }
    /// ```
    #[inline]
    pub fn default_cvc4() -> Self {
        CVC4.default()
    }

    /// Creates a new yices-2-like solver configuration and command.
    ///
    /// # Warning
    ///
    /// The command used to run a particular solver is up to the end-user. As such, it **does not
    /// make sense** to use default commands for anything else than local testing. You should
    /// explicitely pass the command to use with [`Self::yices_2`] instead.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// let conf = SmtConf::default_yices_2();
    /// assert! {
    ///     conf.get_cmd() == "yices" || conf.get_cmd() == "yices.exe"
    /// }
    /// ```
    #[inline]
    pub fn default_yices_2() -> Self {
        Yices2.default()
    }

    /// Spawns the solver.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// let _solver = SmtConf::default_z3().spawn(()).unwrap();
    /// ```
    #[inline]
    pub fn spawn<Parser>(self, parser: Parser) -> SmtRes<Solver<Parser>> {
        Solver::new(self, parser)
    }

    /// Concise description of the underlying solver.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// assert_eq! { SmtConf::default_z3().desc(), "z3" }
    /// ```
    #[inline]
    pub fn desc(&self) -> &str {
        match self.style {
            Z3 => "z3",
            CVC4 => "cvc4",
            Yices2 => "yices2",
        }
    }

    /// Solver command.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// let conf = SmtConf::default_z3();
    /// assert! {
    ///     conf.get_cmd() == "z3" || conf.get_cmd() == "z3.exe"
    /// }
    /// ```
    #[inline]
    pub fn get_cmd(&self) -> &str {
        &self.cmd
    }

    /// Options of the configuration.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// assert_eq! {
    ///     SmtConf::default_z3().get_options(), & [ "-in", "-smt2" ]
    /// }
    /// ```
    #[inline]
    pub fn get_options(&self) -> &[String] {
        &self.options
    }

    /// Adds an option to the configuration.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// let mut conf = SmtConf::default_z3();
    /// conf.option("arith.euclidean_solver=true");
    /// assert_eq! {
    ///     conf.get_options(),
    ///     & [ "-in", "-smt2", "arith.euclidean_solver=true" ]
    /// }
    /// ```
    #[inline]
    pub fn option<S: Into<String>>(&mut self, o: S) -> &mut Self {
        self.options.push(o.into());
        self
    }

    /// Sets the command for the solver.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// let mut conf = SmtConf::default_z3();
    /// conf.cmd("my_custom_z3_command");
    /// assert_eq! { conf.get_cmd(), "my_custom_z3_command" }
    /// ```
    #[inline]
    pub fn cmd<S: Into<String>>(&mut self, cmd: S) -> &mut Self {
        let cmd = cmd.into();
        let mut iter = cmd.split(' ');

        'set_cmd: while let Some(cmd) = iter.next() {
            if !cmd.is_empty() {
                self.cmd = cmd.into();
                break 'set_cmd;
            }
        }

        for option in iter {
            if !option.is_empty() {
                self.options.push(option.into())
            }
        }

        self
    }

    /// Model production flag.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// assert!(SmtConf::default_z3().get_models());
    /// ```
    pub fn get_models(&self) -> bool {
        self.models
    }
    /// Activates model production.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// let mut conf = SmtConf::default_z3();
    /// conf.models();
    /// assert!(conf.get_models());
    /// ```
    pub fn models(&mut self) {
        self.set_models(true)
    }
    /// (De)activates model production.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// let mut conf = SmtConf::default_z3();
    /// conf.set_models(false);
    /// assert!(!conf.get_models());
    /// ```
    pub fn set_models(&mut self, val: bool) {
        self.models = val;
        if val {
            match self.style {
                CVC4 => self.options.push("--produce-models".into()),
                Yices2 => self.options.push("--smt2-model-format".into()),
                Z3 => (),
            }
        }
    }

    /// Incrementality.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// let mut conf = SmtConf::default_z3();
    /// assert!(conf.get_incremental());
    /// ```
    pub fn get_incremental(&self) -> bool {
        self.incremental
    }
    /// Activates incrementality (push/pop, check-sat-assuming).
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// let mut conf = SmtConf::default_z3();
    /// conf.incremental();
    /// assert!(conf.get_incremental());
    /// ```
    pub fn incremental(&mut self) {
        self.set_incremental(true)
    }
    /// Activates incrementality (push/pop, check-sat-assuming).
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// let mut conf = SmtConf::default_z3();
    /// conf.incremental();
    /// assert!(conf.get_incremental());
    /// ```
    pub fn set_incremental(&mut self, val: bool) {
        self.incremental = val;
        if val {
            match self.style {
                CVC4 | Yices2 => self.options.push("--incremental".into()),
                Z3 => (),
            }
        }
    }

    /// Indicates if unsat core production is active.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// assert!(! SmtConf::default_z3().get_unsat_cores());
    /// ```
    #[inline]
    pub fn get_unsat_cores(&self) -> bool {
        self.unsat_cores
    }
    /// Activates unsat core production.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// let mut conf = SmtConf::default_z3();
    /// conf.unsat_cores();
    /// assert!(conf.get_unsat_cores());
    /// ```
    #[inline]
    pub fn unsat_cores(&mut self) {
        self.set_unsat_cores(true)
    }
    /// (De)activates unsat core production.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// let mut conf = SmtConf::default_z3();
    /// conf.set_unsat_cores(false);
    /// assert!(!conf.get_unsat_cores());
    /// ```
    #[inline]
    pub fn set_unsat_cores(&mut self, val: bool) {
        self.unsat_cores = val
    }

    /// Keyword for check-sat with assumptions.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// assert_eq! {
    ///     SmtConf::default_z3().get_check_sat_assuming(), Some("check-sat-assuming")
    /// }
    /// ```
    #[inline]
    pub fn get_check_sat_assuming(&self) -> ConfItem {
        self.check_sat_assuming.as_ref().map(|s| *s)
    }

    /// Indicates if print success is active.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// assert!(! SmtConf::default_z3().get_print_success());
    /// ```
    #[inline]
    #[cfg(not(no_parse_success))]
    pub fn get_print_success(&self) -> bool {
        self.parse_success
    }
    /// Activates parse sucess.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// let mut conf = SmtConf::default_z3();
    /// conf.print_success();
    /// assert!(conf.get_print_success());
    /// ```
    #[inline]
    #[cfg(not(no_parse_success))]
    pub fn print_success(&mut self) {
        self.set_print_success(true)
    }
    /// (De)activates parse sucess.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// let mut conf = SmtConf::default_z3();
    /// conf.set_print_success(true);
    /// assert!(conf.get_print_success());
    /// ```
    #[inline]
    #[cfg(not(no_parse_success))]
    pub fn set_print_success(&mut self, val: bool) {
        self.parse_success = val
    }

    /// Indicates if interpolant production is active.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// assert!(SmtConf::default_z3().get_interpolants());
    /// ```
    #[inline]
    pub fn get_interpolants(&self) -> bool {
        self.interpolants
    }
    /// Activates interpolant production.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// let mut conf = SmtConf::default_z3();
    /// conf.interpolants();
    /// assert!(conf.get_interpolants());
    /// ```
    #[inline]
    pub fn interpolants(&mut self) -> SmtRes<()> {
        self.set_interpolants(true)
    }
    /// (De)activates interpolant production.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// let mut conf = SmtConf::default_z3();
    /// conf.set_interpolants(false);
    /// assert!(!conf.get_interpolants());
    /// ```
    #[inline]
    pub fn set_interpolants(&mut self, val: bool) -> SmtRes<()> {
        if self.style.is_z3() {
            self.interpolants = val;
            Ok(())
        } else {
            bail!(
                "interpolant production is only supported by Z3, \
                cannot activate interpolants for `{}`",
                self.style,
            )
        }
    }
}

/// ## Solver-specific error-handling
impl SmtConf {
    /// Adds information to a `get-value` error message if needed.
    pub fn enrich_get_values_error(&self, e: crate::errors::Error) -> crate::errors::Error {
        match self.style {
            SmtStyle::CVC4 => e.chain_err(|| {
                "some versions of CVC4 produce errors on `get-value` commands, \
                 consider using `get-model` instead"
            }),
            SmtStyle::Z3 | SmtStyle::Yices2 => e,
        }
    }
}
