//! Solver configuration, contains backend-solver-specific info.
//!
//! Do **NOT** use wildcards when matching over `SmtStyle`. We want the code to fail to compile
//! whenever we add a solver. Likewise, do not use `if let` with `SmtStyle`.

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

/// Solver styles.
///
/// - [z3][z3]: full support
/// - [cvc4][cvc4]: full support in theory, but only partially tested. Note that `get-value` is
///   known to crash some versions of CVC4.
/// - [Alt-Ergo][alt-ergo]: full support in theory, but only partially tested.
/// - [yices 2][yices 2]: full support in theory, but only partially tested. Command `get-model`
///   will only work on Yices 2 > `2.6.1`, and needs to be activated in [SmtConf][SmtConf] with
///   [`conf.models()`](struct.SmtConf.html#method.models). To understand why, see
///   <https://github.com/SRI-CSL/yices2/issues/162>.
///
/// [z3]: https://github.com/Z3Prover/z3 (z3 github repository)
/// [cvc4]: https://cvc4.github.io/ (cvc4 github pages)
/// [alt-ergo]: https://github.com/OCamlPro/alt-ergo/ (Alt-Ergo github pages)
/// [yices 2]: https://yices.csl.sri.com/ (yices 2 official page)
#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
pub enum SmtStyle {
    /// Z3-style smt solver.
    Z3,
    /// CVC4-style smt solver.
    ///
    /// **NB**: CVC4 has only been partially tested at this point.
    CVC4,
    /// Alt-Ergo-style smt solver.
    ///
    /// **NB**: Alt-Ergo has only been partially tested at this point.
    AltErgo,
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
                check_sat_assuming: unsupported(),
            },
            AltErgo => SmtConf {
                style: self,
                cmd,
                options: vec![],
                models: false,
                incremental: false,
                parse_success: false,
                unsat_cores: false,
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
    /// explicitely pass the command to use with [`Self::new`](#method.new) instead.
    pub fn default(self) -> SmtConf {
        self.new(self.cmd())
    }

    /// A solver style from a string.
    #[allow(dead_code)]
    pub fn of_str(s: &str) -> Option<Self> {
        match s {
            "z3" | "Z3" => Some(Z3),
            "cvc4" | "CVC4" => Some(CVC4),
            "alt-ergo" | "ALT-ERGO" | "alt ergo" | "ALT ERGO" | "altergo" | "AltErgo" => Some(CVC4),
            "Yices2" | "yices2" | "YICES2" | "Yices 2" | "yices 2" | "YICES 2" => Some(CVC4),
            _ => None,
        }
    }
    /// Legal string representations of solver styles.
    #[allow(dead_code)]
    pub fn str_keys() -> Vec<&'static str> {
        vec![
            "z3", "Z3", "cvc4", "CVC4", "alt-ergo", "ALT-ERGO", "alt ergo", "ALT ERGO", "altergo",
            "AltErgo", "Yices2", "yices2", "YICES2", "Yices 2", "yices 2", "YICES 2",
        ]
    }

    /// Default command for a solver style.
    #[cfg(not(windows))]
    pub fn cmd(self) -> String {
        match self {
            Z3 => "z3".to_string(),
            CVC4 => "cvc4".to_string(),
            AltErgo => "alt-ergo".to_string(),
            Yices2 => "yices".to_string(),
        }
    }
    /// Default command for a solver style.
    #[cfg(windows)]
    pub fn cmd(self) -> String {
        match self {
            Z3 => "z3.exe".to_string(),
            CVC4 => "cvc4.exe".to_string(),
            AltErgo => "alt-ergo.exe".to_string(),
            Yices2 => "yices.exe".to_string(),
        }
    }
}

impl fmt::Display for SmtStyle {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Z3 => write!(fmt, "z3"),
            CVC4 => write!(fmt, "cvc4"),
            AltErgo => write!(fmt, "Alt-Ergo"),
            Yices2 => write!(fmt, "yices2"),
        }
    }
}

/// Configuration and solver specific info.
///
/// - [z3][z3]: full support
/// - [cvc4][cvc4]: full support in theory, but only partially tested. Note that `get-value` is
///   known to crash some versions of CVC4.
/// - [Alt-Ergo][alt-ergo]: full support in theory, but only partially tested.
/// - [yices 2][yices 2]: full support in theory, but only partially tested. Command `get-model`
///   will only work on Yices 2 > `2.6.1`, and needs to be activated in [SmtConf][SmtConf] with
///   [`conf.models()`](struct.SmtConf.html#method.models). To understand why, see
///   <https://github.com/SRI-CSL/yices2/issues/162>.
///
/// [z3]: https://github.com/Z3Prover/z3 (z3 github repository)
/// [cvc4]: https://cvc4.github.io/ (cvc4 github pages)
/// [alt-ergo]: https://github.com/OCamlPro/alt-ergo/ (Alt-Ergo github pages)
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
    /// Keyword for check-sat with assumptions.
    check_sat_assuming: ConfItem,
}

impl SmtConf {
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

    /// Creates a new Alt-Ergo-like solver configuration.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// let conf = SmtConf::alt_ergo("my_alt-ergo_command");
    /// assert!(conf.get_cmd() == "my_alt-ergo_command")
    /// ```
    #[inline]
    pub fn alt_ergo(cmd: impl Into<String>) -> Self {
        AltErgo.new(cmd)
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

    /// Creates a new z3-like solver configuration and command.
    ///
    /// # Warning
    ///
    /// The command used to run a particular solver is up to the end-user. As such, it **does not
    /// make sense** to use default commands for anything else than local testing. You should
    /// explicitely pass the command to use with [`Self::z3`](#method.z3) instead.
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
    /// explicitely pass the command to use with [`Self::cvc4`](#method.cvc4) instead.
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

    /// Creates a new alt-ergo-like solver configuration and command.
    ///
    /// # Warning
    ///
    /// The command used to run a particular solver is up to the end-user. As such, it **does not
    /// make sense** to use default commands for anything else than local testing. You should
    /// explicitely pass the command to use with [`Self::alt_ergo`](#method.alt_ergo) instead.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// let conf = SmtConf::default_alt_ergo();
    /// assert! {
    ///     conf.get_cmd() == "alt-ergo" || conf.get_cmd() == "alt-ergo.exe"
    /// }
    /// ```
    #[inline]
    pub fn default_alt_ergo() -> Self {
        AltErgo.default()
    }

    /// Creates a new yices-2-like solver configuration and command.
    ///
    /// # Warning
    ///
    /// The command used to run a particular solver is up to the end-user. As such, it **does not
    /// make sense** to use default commands for anything else than local testing. You should
    /// explicitely pass the command to use with [`Self::yices_2`](#method.yices_2) instead.
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
            AltErgo => "alt-ergo",
            Yices2 => "yices2",
        }
    }

    /// Model production flag.
    pub fn get_models(&self) -> bool {
        self.models
    }
    /// Activates model production.
    pub fn models(&mut self) {
        if self.models {
            return ();
        } else {
            self.models = true
        }
        match self.style {
            CVC4 => self.options.push("--produce-models".into()),
            AltErgo => self.options.push("-mcomplete".into()),
            Yices2 => self.options.push("--smt2-model-format".into()),
            Z3 => (),
        }
    }

    /// Incrementality.
    pub fn get_incremental(&self) -> bool {
        self.incremental
    }
    /// Activates incrementality (push/pop, check-sat-assuming).
    pub fn incremental(&mut self) {
        if self.incremental {
            return ();
        } else {
            self.incremental = true
        }
        match self.style {
            CVC4 | Yices2 => self.options.push("--incremental".into()),
            AltErgo | Z3 => (),
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

    /// Indicates if print success is active.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// assert! { ! SmtConf::default_z3().get_print_success() }
    /// ```
    #[inline]
    pub fn get_print_success(&self) -> bool {
        self.parse_success
    }

    /// Indicates if unsat cores is active.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// assert! { ! SmtConf::default_z3().get_unsat_cores() }
    /// ```
    #[inline]
    pub fn get_unsat_cores(&self) -> bool {
        self.unsat_cores
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

    /// Activates parse sucess.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// let mut conf = SmtConf::default_z3();
    /// conf.print_success();
    /// assert! { conf.get_print_success() }
    /// ```
    #[inline]
    #[cfg(not(no_parse_success))]
    pub fn print_success(&mut self) {
        self.parse_success = true
    }

    /// Activates unsat-core production.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::SmtConf;
    /// let mut conf = SmtConf::default_z3();
    /// conf.unsat_cores();
    /// assert! { conf.get_unsat_cores() }
    /// ```
    #[inline]
    pub fn unsat_cores(&mut self) {
        self.unsat_cores = true
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
            SmtStyle::Z3 | SmtStyle::AltErgo | SmtStyle::Yices2 => e,
        }
    }
}
