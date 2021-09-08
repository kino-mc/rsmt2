//! Wrapper around an SMT Lib 2 compliant solver.
//!
//! The underlying solver runs in a separate process, communication goes through system pipes.

use std::fs::File;
use std::io::{BufReader, BufWriter, Read, Write};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};

use crate::{
    actlit::Actlit,
    common::*,
    conf::SmtConf,
    parse::{ExprParser, IdentParser, ModelParser, RSmtParser, SymParser, ValueParser},
};

/// Promise for an asynchronous check-sat.
pub struct FutureCheckSat {
    _nothing: (),
}
fn future_check_sat() -> FutureCheckSat {
    FutureCheckSat { _nothing: () }
}

/// Solver providing most of the SMT-LIB 2.5 commands.
///
/// Note the [`Self::tee`] function, which takes a file writer to which it will write
/// everything sent to the solver.
pub struct Solver<Parser> {
    /// Solver configuration.
    conf: SmtConf,
    /// Actual solver process.
    kid: Child,
    /// Solver's stdin.
    stdin: BufWriter<ChildStdin>,
    /// Tee file writer.
    tee: Option<BufWriter<File>>,
    /// Parser on the solver's stdout.
    smt_parser: RSmtParser,
    /// User-defined parser.
    parser: Parser,
    /// Actlit counter.
    actlit: usize,
}

impl<Parser> Write for Solver<Parser> {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        if let Some(tee) = self.tee.as_mut() {
            let _ = tee.write(buf);
        }
        self.stdin.write(buf)
    }
    fn flush(&mut self) -> ::std::io::Result<()> {
        if let Some(tee) = self.tee.as_mut() {
            let _ = tee.flush();
        }
        self.stdin.flush()
    }
}

impl<Parser> Read for Solver<Parser> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.smt_parser.read(buf)
    }
}

/// Writes something in both the solver and the teed output.
macro_rules! tee_write {
  ($slf:expr, |$w:ident| $($tail:tt)*) => ({
    if let Some(ref mut $w) = $slf.tee {
      $($tail)*;
      writeln!($w)?;
      $w.flush() ?
    }
    let $w = & mut $slf.stdin;
    $($tail)*;
    $w.flush() ?
  });
}

impl<Parser> ::std::ops::Drop for Solver<Parser> {
    fn drop(&mut self) {
        let _ = self.kill();
        ()
    }
}

/// # Basic functions, not related to SMT-LIB.
impl<Parser> Solver<Parser> {
    /// Spawns the solver kid.
    fn spawn(conf: &SmtConf) -> SmtRes<(Child, BufWriter<ChildStdin>, BufReader<ChildStdout>)> {
        let mut kid = Command::new(
            // Command.
            conf.get_cmd(),
        )
        .args(
            // Options.
            conf.get_options(),
        )
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .chain_err::<_, ErrorKind>(|| {
            format!(
                "While spawning child process with {}",
                conf.get_cmd().to_string()
            )
            .into()
        })?;

        let mut stdin_opt = None;
        ::std::mem::swap(&mut stdin_opt, &mut kid.stdin);

        let stdin = if let Some(inner) = stdin_opt {
            BufWriter::new(inner)
        } else {
            bail!("could not retrieve solver's stdin")
        };

        let mut stdout_opt = None;
        ::std::mem::swap(&mut stdout_opt, &mut kid.stdout);

        let stdout = if let Some(inner) = stdout_opt {
            BufReader::new(inner)
        } else {
            bail!("could not retrieve solver's stdout")
        };

        Ok((kid, stdin, stdout))
    }

    /// Constructor.
    pub fn new(conf: SmtConf, parser: Parser) -> SmtRes<Self> {
        // Constructing command and spawning kid.
        let (kid, stdin, stdout) = Self::spawn(&conf)?;

        let smt_parser = RSmtParser::new(stdout);

        let tee = None;
        let actlit = 0;

        let mut slf = Solver {
            kid,
            stdin,
            tee,
            conf,
            smt_parser,
            parser,
            actlit,
        };

        if slf.conf.get_models() {
            slf.produce_models()?;
        }
        if slf.conf.get_unsat_cores() {
            slf.produce_unsat_cores()?;
        }

        Ok(slf)
    }

    /// Creates a solver kid with the default z3 configuration.
    ///
    /// Mostly used in tests, same as `Self::new( SmtConf::z3(), parser )`.
    pub fn z3(parser: Parser, cmd: impl Into<String>) -> SmtRes<Self> {
        Self::new(SmtConf::z3(cmd), parser)
    }
    /// Creates a solver kid with the default cvc4 configuration.
    ///
    /// Mostly used in tests, same as `Self::new( SmtConf::z3(), parser )`.
    pub fn cvc4(parser: Parser, cmd: impl Into<String>) -> SmtRes<Self> {
        Self::new(SmtConf::cvc4(cmd), parser)
    }
    /// Creates a solver kid with the default yices 2 configuration.
    ///
    /// Mostly used in tests, same as `Self::new( SmtConf::yices_2(), parser )`.
    pub fn yices_2(parser: Parser, cmd: impl Into<String>) -> SmtRes<Self> {
        Self::new(SmtConf::yices_2(cmd), parser)
    }

    /// Creates a solver kid with the default z3 configuration and command.
    ///
    /// Mostly used in tests, same as `Self::new( SmtConf::default_z3(), parser )`.
    ///
    /// # Warning
    ///
    /// The command used to run a particular solver is up to the end-user. As such, it **does not
    /// make sense** to use default commands for anything else than local testing. You should
    /// explicitely pass the command to use with [`Self::z3`] instead.
    pub fn default_z3(parser: Parser) -> SmtRes<Self> {
        Self::new(SmtConf::default_z3(), parser)
    }

    /// Creates a solver kid with the default cvc4 configuration and
    /// command.
    ///
    /// Mostly used in tests, same as `Self::new( SmtConf::default_z3(), parser )`.
    ///
    /// # Warning
    ///
    /// The command used to run a particular solver is up to the end-user. As such, it **does not
    /// make sense** to use default commands for anything else than local testing. You should
    /// explicitely pass the command to use with [`Self::cvc4`] instead.
    pub fn default_cvc4(parser: Parser) -> SmtRes<Self> {
        Self::new(SmtConf::default_cvc4(), parser)
    }

    /// Creates a solver kid with the default yices 2 configuration and
    /// command.
    ///
    /// Mostly used in tests, same as `Self::new( SmtConf::default_yices_2(), parser )`.
    ///
    /// # Warning
    ///
    /// The command used to run a particular solver is up to the end-user. As such, it **does not
    /// make sense** to use default commands for anything else than local testing. You should
    /// explicitely pass the command to use with [`Self::yices_2`] instead.
    pub fn default_yices_2(parser: Parser) -> SmtRes<Self> {
        Self::new(SmtConf::default_yices_2(), parser)
    }

    /// Returns the configuration of the solver.
    pub fn conf(&self) -> &SmtConf {
        &self.conf
    }

    /// Forces the solver to write all communications to a file.
    ///
    /// - fails if the solver is already tee-ed;
    /// - see also [`Self::path_tee`].
    pub fn tee(&mut self, file: File) -> SmtRes<()> {
        if self.tee.is_some() {
            bail!("Trying to tee a solver that's already tee-ed")
        }
        let mut tee = BufWriter::with_capacity(1000, file);
        write!(tee, "; Command:\n; > {}", self.conf.get_cmd())?;
        for option in self.conf.get_options() {
            write!(tee, " {}", option)?
        }
        writeln!(tee, "\n")?;
        self.tee = Some(tee);
        Ok(())
    }

    /// Forces the solver to write all communications to a file.
    ///
    /// - opens `file` with `create` and `write`;
    /// - fails if the solver is already tee-ed;
    /// - see also [`Self::tee`].
    pub fn path_tee<P>(&mut self, path: P) -> SmtRes<()>
    where
        P: AsRef<::std::path::Path>,
    {
        use std::fs::OpenOptions;

        let path: &::std::path::Path = path.as_ref();
        let file = OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(path)
            .chain_err(|| format!("while opening tee file `{}`", path.to_string_lossy()))?;
        self.tee(file)
    }

    /// True if the solver is tee-ed.
    pub fn is_teed(&self) -> bool {
        self.tee.is_some()
    }

    /// Kills the solver kid.
    ///
    /// The windows version just prints `(exit)` on the kid's `stdin`. Anything else seems to cause
    /// problems.
    ///
    /// This function is automatically called when the solver is dropped.
    #[cfg(windows)]
    pub fn kill(&mut self) -> SmtRes<()> {
        let _ = writeln!(self.stdin, "(exit)");
        let _ = self.stdin.flush();
        let _ = self.kid.kill();
        Ok(())
    }
    /// Kills the solver kid.
    ///
    /// The windows version just prints `(exit)` on the kid's `stdin`. Anything else seems to cause
    /// problems.
    ///
    /// This function is automatically called when the solver is dropped.
    #[cfg(not(windows))]
    pub fn kill(&mut self) -> SmtRes<()> {
        let _ = writeln!(self.stdin, "(exit)");
        let _ = self.stdin.flush();
        let _ = self.kid.kill();
        let join = self
            .kid
            .try_wait()
            .chain_err(|| "waiting for child process to exit")?;
        if join.is_none() {
            self.kid
                .kill()
                .chain_err::<_, ErrorKind>(|| "while killing child process".into())?
        }
        Ok(())
    }

    /// Internal comment function.
    #[inline]
    fn cmt(file: &mut BufWriter<File>, blah: &str) -> SmtRes<()> {
        for line in blah.lines() {
            writeln!(file, "; {}", line)?
        }
        file.flush()?;
        Ok(())
    }

    /// Prints a comment in the tee-ed file, if any.
    #[inline]
    pub fn comment_args(&mut self, args: std::fmt::Arguments) -> SmtRes<()> {
        if let Some(ref mut file) = self.tee {
            Self::cmt(file, &format!("{}", args))?
        }
        Ok(())
    }

    /// Prints a comment in the tee-ed file, if any (string version).
    #[inline]
    pub fn comment(&mut self, blah: &str) -> SmtRes<()> {
        if let Some(ref mut file) = self.tee {
            Self::cmt(file, blah)?
        }
        Ok(())
    }
}

/// # Basic SMT-LIB parser-agnostic commands.
impl<Parser> Solver<Parser> {
    /// Asserts an expression.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::Solver;
    /// let mut solver = Solver::default_z3(()).unwrap();
    /// solver.assert("(= 0 1)").unwrap();
    /// ```
    #[inline]
    pub fn assert(&mut self, expr: impl Expr2Smt) -> SmtRes<()> {
        self.assert_with(expr, ())
    }

    /// Check-sat command, turns `unknown` results into errors.
    ///
    /// # See also
    ///
    /// - [`Self::print_check_sat`]
    /// - [`Self::parse_check_sat`]
    ///
    /// If you want a more natural way to handle unknown results, see `parse_check_sat_or_unk`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::prelude::*;
    /// let mut conf = SmtConf::default_z3();
    /// conf.option("-t:10");
    /// let mut solver = Solver::new(conf, ()).unwrap();
    /// solver.declare_const("x", "Int").unwrap();
    /// solver.declare_const("y", "Int").unwrap();
    ///
    /// solver.push(1).unwrap();
    /// solver.assert("(= (+ x y) 0)").unwrap();
    /// let maybe_sat = solver.check_sat().unwrap();
    /// assert_eq! { maybe_sat, true }
    /// solver.pop(1).unwrap();
    ///
    /// solver.assert("(= (+ (* x x y) (* y y x)) 7654321)").unwrap();
    /// let sat_res = & solver.check_sat();
    ///
    /// match * sat_res {
    ///     Err(ref e) => match * e.kind() {
    ///         ::rsmt2::errors::ErrorKind::Unknown => (),
    ///         _ => panic!("expected unknown"),
    ///     },
    ///     Ok(res) => panic!("expected error: {:?}", res),
    /// }
    /// ```
    pub fn check_sat(&mut self) -> SmtRes<bool> {
        let future = self.print_check_sat()?;
        self.parse_check_sat(future)
    }

    /// Check-sat command, turns `unknown` results in `None`.
    ///
    /// # See also
    ///
    /// - [`Self::parse_check_sat_or_unk`]
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::prelude::*;
    /// let mut conf = SmtConf::default_z3();
    /// conf.option("-t:10");
    /// # let mut solver = Solver::new(conf, ()).unwrap();
    /// solver.path_tee("./log.smt2").unwrap();
    /// solver.declare_const("x", "Int").unwrap();
    /// solver.declare_const("y", "Int").unwrap();
    ///
    /// solver.push(1).unwrap();
    /// solver.assert("(= (+ x y) 0)").unwrap();
    /// let maybe_sat = solver.check_sat_or_unk().unwrap();
    /// assert_eq! { maybe_sat, Some(true) }
    /// solver.pop(1).unwrap();
    ///
    /// solver.assert("(= (+ (* x x y) (* y y x)) 7654321)").unwrap();
    /// let maybe_sat = solver.check_sat_or_unk().unwrap();
    /// // Unknown ~~~~~~~~~~~~~vvvv
    /// assert_eq! { maybe_sat, None }
    /// ```
    pub fn check_sat_or_unk(&mut self) -> SmtRes<Option<bool>> {
        let future = self.print_check_sat()?;
        self.parse_check_sat_or_unk(future)
    }

    /// Resets the underlying solver. Restarts the kid process if no reset command is supported.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::Solver;
    /// let mut solver = Solver::default_z3(()).unwrap();
    /// solver.assert("(= 0 1)").unwrap();
    /// assert!(! solver.check_sat().unwrap());
    /// solver.reset().unwrap();
    /// assert!(solver.check_sat().unwrap());
    /// ```
    #[inline]
    pub fn reset(&mut self) -> SmtRes<()> {
        self.actlit = 0;
        tee_write! {
          self, |w| write_str(w, "(reset)\n") ?
        }
        Ok(())
    }

    /// Declares a new constant.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::Solver;
    /// let mut solver = Solver::default_z3(()).unwrap();
    /// solver.declare_const("x", "Int").unwrap()
    /// ```
    #[inline]
    pub fn declare_const(&mut self, symbol: impl Sym2Smt, out_sort: impl Sort2Smt) -> SmtRes<()> {
        self.declare_const_with(symbol, out_sort, ())
    }

    /// Declares a new function symbol.
    ///
    /// ```rust
    /// # use rsmt2::Solver;
    /// let mut solver = Solver::default_z3(()).unwrap();
    /// solver.declare_fun(
    ///     "my_symbol", & [ "Int", "Real", "Bool" ], "Bool"
    /// ).unwrap()
    /// ```
    #[inline]
    pub fn declare_fun<FunSym, Args, OutSort>(
        &mut self,
        symbol: FunSym,
        args: Args,
        out: OutSort,
    ) -> SmtRes<()>
    where
        FunSym: Sym2Smt<()>,
        OutSort: Sort2Smt,
        Args: IntoIterator,
        Args::Item: Sort2Smt,
    {
        self.declare_fun_with(symbol, args, out, ())
    }

    /// Defines a new constant function symbol.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::Solver;
    /// let mut solver = Solver::default_z3(()).unwrap();
    /// solver.define_const(
    ///     "seven", "Int", "7"
    /// ).unwrap()
    /// ```
    #[inline]
    pub fn define_const(
        &mut self,
        symbol: impl Sym2Smt,
        out: impl Sort2Smt,
        body: impl Expr2Smt,
    ) -> SmtRes<()> {
        self.define_const_with(symbol, out, body, ())
    }

    /// Defines a new function symbol.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::Solver;
    /// let mut solver = Solver::default_z3(()).unwrap();
    /// solver.define_fun(
    ///     "abs", & [ ("n", "Int") ], "Int", "(ite (< x 0) (- x) x)"
    /// ).unwrap()
    /// ```
    #[inline]
    pub fn define_fun<Args>(
        &mut self,
        symbol: impl Sym2Smt,
        args: Args,
        out: impl Sort2Smt,
        body: impl Expr2Smt,
    ) -> SmtRes<()>
    where
        Args: IntoIterator,
        Args::Item: SymAndSort,
    {
        self.define_fun_with(symbol, args, out, body, ())
    }

    /// Pushes `n` layers on the assertion stack.
    ///
    /// - see also [`Self::pop`].
    ///
    /// Note that using [actlits][crate::actlit] is more efficient than push/pop, and is useable for
    /// most push/pop use-cases.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::Solver;
    /// let mut solver = Solver::default_z3(()).unwrap();
    /// solver.declare_const("x", "Int").unwrap();
    /// solver.declare_const("y", "Int").unwrap();
    /// solver.assert("(= x y)").unwrap();
    /// let sat = solver.check_sat().unwrap();
    /// assert!(sat);
    ///
    /// solver.push(1).unwrap();
    /// solver.assert("(= x (+ x 1))").unwrap();
    /// let sat = solver.check_sat().unwrap();
    /// assert!(! sat);
    /// solver.pop(1).unwrap();
    ///
    /// let sat = solver.check_sat().unwrap();
    /// assert!(sat);
    /// ```
    #[inline]
    pub fn push(&mut self, n: u8) -> SmtRes<()> {
        tee_write! {
          self, |w| writeln!(w, "(push {})", n) ?
        }
        Ok(())
    }

    /// Pops `n` layers off the assertion stack.
    ///
    /// - see also [`Self::push`].
    ///
    /// Note that using [actlits][crate::actlit] is more efficient than push/pop, and is useable for
    /// most push/pop use-cases.
    #[inline]
    pub fn pop(&mut self, n: u8) -> SmtRes<()> {
        tee_write! {
          self, |w| writeln!(w, "(pop {})", n) ?
        }
        Ok(())
    }

    /// Check-sat assuming command, turns `unknown` results into errors.
    ///
    /// - see also [actlits][crate::actlit].
    pub fn check_sat_assuming<Idents>(&mut self, idents: Idents) -> SmtRes<bool>
    where
        Idents: IntoIterator,
        Idents::Item: Sym2Smt,
    {
        self.check_sat_assuming_with(idents, ())
    }

    /// Check-sat assuming command, turns `unknown` results into `None`.
    ///
    /// - see also [actlits][crate::actlit].
    pub fn check_sat_assuming_or_unk<Ident, Idents>(
        &mut self,
        idents: Idents,
    ) -> SmtRes<Option<bool>>
    where
        Idents: IntoIterator,
        Idents::Item: Sym2Smt,
    {
        self.check_sat_assuming_or_unk_with(idents, ())
    }

    /// Sets the logic.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::{SmtConf, Solver};
    /// let mut solver = Solver::default_z3(()).unwrap();
    /// solver.set_logic( ::rsmt2::Logic::QF_UF ).unwrap();
    /// ```
    #[inline]
    pub fn set_logic(&mut self, logic: Logic) -> SmtRes<()> {
        tee_write! {
          self, |w| {
            write_str(w, "(set-logic ")?;
            logic.to_smt2(w, ())?;
            write_str(w, ")\n") ?
          }
        }
        Ok(())
    }

    /// Sets a custom logic.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::{SmtConf, Solver};
    /// let mut solver = Solver::default_z3(()).unwrap();
    /// solver.set_custom_logic("QF_UFBV").unwrap();
    /// ```
    #[inline]
    pub fn set_custom_logic(&mut self, logic: impl AsRef<str>) -> SmtRes<()> {
        tee_write! {
          self, |w| {
            write_str(w, "(set-logic ")?;
            write_str(w, logic.as_ref())?;
            write_str(w, ")\n") ?
          }
        }
        Ok(())
    }

    /// Defines a recursive function.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::Solver;
    /// let mut solver = Solver::default_z3(()).unwrap();
    /// solver.define_fun_rec(
    ///     "abs", & [ ("n", "Int") ], "Int", "(ite (< x 0) (abs (- x)) x)"
    /// ).unwrap()
    /// ```
    #[inline]
    pub fn define_fun_rec<Args>(
        &mut self,
        symbol: impl Sym2Smt,
        args: Args,
        out: impl Sort2Smt,
        body: impl Expr2Smt,
    ) -> SmtRes<()>
    where
        Args: IntoIterator,
        Args::Item: SymAndSort,
    {
        self.define_fun_rec_with(symbol, args, out, body, ())
    }

    /// Defines some (possibily mutually) recursive functions.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::Solver;
    /// let mut solver = Solver::default_z3(()).unwrap();
    /// solver.define_funs_rec( & [
    ///     ("abs_1", [ ("n", "Int") ], "Int", "(ite (< x 0) (abs_2 (- x)) x)"),
    ///     ("abs_2", [ ("n", "Int") ], "Int", "(ite (< x 0) (abs_3 (- x)) x)"),
    ///     ("abs_3", [ ("n", "Int") ], "Int", "(ite (< x 0) (abs_1 (- x)) x)"),
    /// ] ).unwrap()
    /// ```
    #[inline]
    pub fn define_funs_rec<Defs>(&mut self, funs: Defs) -> SmtRes<()>
    where
        Defs: IntoIterator + Clone,
        Defs::Item: FunDef,
    {
        self.define_funs_rec_with(funs, ())
    }

    /// Declares mutually recursive datatypes.
    ///
    /// A relatively recent version of z3 is recommended. Sort definition is a relatively expert
    /// action, this function is a bit complex. The example below goes over how it works.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rsmt2::print::{SortDecl, SortField, SortVariant};
    ///
    /// // Alright, so we're going to declare two mutually recursive sorts. It is easier to pack the
    /// // sort-declaration data in custom types. If you want to declare a sort, you most likely
    /// // already have a representation for it, so working on custom types is reasonable.
    ///
    /// // Notice that the `SortDecl`, `SortField` and `SortVariant` traits from `rsmt2::print::_` are in
    /// // scope. This is what our custom types will need to generate to declare the sort.
    ///
    /// // We'll use static string slices for simplicity as `&str` implements all printing traits.
    /// type Sym = &'static str;
    /// type Sort = &'static str;
    ///
    /// // Let's start with the top-level sort type.
    /// struct MySort {
    ///     // Name of the sort, for instance `List`.
    ///     sym: Sym,
    ///     // Symbol(s) for the type parameter(s), for instance `T` for `List<T>`. Must be a collection
    ///     // of known length, because rsmt2 needs to access the arity (number of type parameters).
    ///     args: Vec<Sym>,
    ///     // Body of the sort: its variants. For instance the `nil` and `cons` variants for `List<T>`.
    ///     variants: Vec<Variant>,
    /// }
    /// impl MySort {
    ///     // This thing build the actual definition expected by rsmt2. Its output is something that
    ///     // implements `SortDecl` and can only live as long as the input ref to `self`.
    ///     fn as_decl<'me>(&'me self) -> impl SortDecl + 'me {
    ///         // Check out rsmt2's documentation and you'll see that `SortDecl` is already implemented for
    ///         // certain triplets.
    ///         (
    ///             // Symbol.
    ///             &self.sym,
    ///             // Sized collection of type-parameter symbols.
    ///             &self.args,
    ///             // Variant, collection of iterator over `impl SortVariant` (see below).
    ///             self.variants.iter().map(Variant::as_decl),
    ///         )
    ///     }
    ///
    ///     fn tree() -> Self {
    ///         Self {
    ///             sym: "Tree",
    ///             args: vec!["T"],
    ///             variants: vec![Variant::tree_leaf(), Variant::tree_node()],
    ///         }
    ///     }
    /// }
    ///
    /// // Next up, variants. A variant is a symbol (*e.g.* `nil` or `cons` for `List<T>`) and some
    /// // fields which describe the data stored in the variant.
    /// struct Variant {
    ///     sym: Sym,
    ///     fields: Vec<Field>,
    /// }
    /// impl Variant {
    ///     // Variant declaration; again, `SortVariant` is implemented for certain types of pairs.
    ///     fn as_decl<'me>(&'me self) -> impl SortVariant + 'me {
    ///         (
    ///             // Symbol.
    ///             self.sym,
    ///             // Iterator over field declarations.
    ///             self.fields.iter().map(Field::as_decl),
    ///         )
    ///     }
    ///
    ///     fn tree_leaf() -> Self {
    ///         Self {
    ///             sym: "leaf",
    ///             fields: vec![],
    ///         }
    ///     }
    ///     fn tree_node() -> Self {
    ///         Self {
    ///             sym: "node",
    ///             fields: vec![Field::tree_node_value(), Field::tree_node_children()],
    ///         }
    ///     }
    /// }
    ///
    /// // A symbol and a sort: describes a piece of data in a variant with a symbol to retrieve it,
    /// // *i.e.* the name of the field.
    /// struct Field {
    ///     sym: Sym,
    ///     sort: Sort,
    /// }
    /// impl Field {
    ///     // As usual, `SortField` is implemented for certain pairs.
    ///     fn as_decl(&self) -> impl SortField {
    ///         (self.sym, self.sort)
    ///     }
    ///
    ///     fn tree_node_value() -> Self {
    ///         Self {
    ///             sym: "value",
    ///             sort: "T",
    ///         }
    ///     }
    ///     fn tree_node_children() -> Self {
    ///         Self {
    ///             sym: "children",
    ///             sort: "(TreeList T)",
    ///         }
    ///     }
    /// }
    ///
    /// let tree = MySort::tree();
    ///
    /// // Now this `tree` uses an non-existing `(TreeList T)` sort to store its children, let's declare
    /// // it now.
    ///
    /// let nil = Variant {
    ///     sym: "nil",
    ///     fields: vec![],
    /// };
    /// let cons = Variant {
    ///     sym: "cons",
    ///     fields: vec![
    ///         Field {
    ///             sym: "car",
    ///             sort: "(Tree T)",
    ///         },
    ///         Field {
    ///             sym: "cdr",
    ///             sort: "(TreeList T)",
    ///         },
    ///     ],
    /// };
    /// let tree_list = MySort {
    ///     sym: "TreeList",
    ///     args: vec!["T"],
    ///     variants: vec![nil, cons],
    /// };
    ///
    /// let mut solver = rsmt2::Solver::default_z3(()).unwrap();
    ///
    /// solver
    ///     // These sort are mutually recursive, `Solver::declare_datatypes` needs to declare them at the
    ///     // same time.
    ///     .declare_datatypes(&[tree.as_decl(), tree_list.as_decl()])
    ///     .unwrap();
    ///
    /// // That's it! Solver now knows these sorts and we can use them.
    ///
    /// solver.declare_const("t1", "(Tree Int)").unwrap();
    /// solver.declare_const("t2", "(Tree Bool)").unwrap();
    ///
    /// solver.assert("(> (value t1) 20)").unwrap();
    /// solver.assert("(not (is-leaf t2))").unwrap();
    /// solver.assert("(not (value t2))").unwrap();
    ///
    /// let sat = solver.check_sat().unwrap();
    /// assert!(sat);
    /// ```
    pub fn declare_datatypes<Defs>(&mut self, defs: Defs) -> SmtRes<()>
    where
        Defs: IntoIterator + Clone,
        Defs::Item: SortDecl,
    {
        tee_write! {
          self, |w| write!(w, "(declare-datatypes (") ?
        }

        for def in defs.clone() {
            let sort_sym = def.sort_sym();
            let arity = def.arity();
            tee_write! {
              self, |w| {
                write!(w, " (")?;
                sort_sym.sym_to_smt2(w, ())?;
                write!(w, " {})", arity) ?
              }
            }
        }

        tee_write! {
          self, |w| write!(w, " ) (") ?
        }

        for def in defs {
            let arity = def.arity();
            let args = def.args();
            let variants = def.variants();
            tee_write! { self, |w| write!(w, " (")? };
            if arity > 0 {
                tee_write! { self, |w| write!(w, "par (")? };
                for param in args {
                    tee_write! { self, |w| {
                        write!(w, " ")?;
                        param.sym_to_smt2(w, ())?;
                    }}
                }
                tee_write! { self, |w| write!(w, " ) (")? };
            }

            for variant in variants {
                let sym = variant.sym();
                let mut fields = variant.fields();
                let first_field = fields.next();

                tee_write! { self, |w| write!(w, " ")? };

                if first_field.is_some() {
                    tee_write! { self, |w| write!(w, "(")? };
                }

                tee_write! { self, |w| sym.sym_to_smt2(w, ())? };

                if let Some(first) = first_field {
                    for field in Some(first).into_iter().chain(fields) {
                        let sym = field.sym();
                        let sort = field.sort();
                        tee_write! {
                            self, |w| {
                                write!(w, " (")?;
                                sym.sym_to_smt2(w, ())?;
                                write!(w, " ")?;
                                sort.sort_to_smt2(w)?;
                                write!(w, ")")?;
                            }
                        }
                    }

                    tee_write! { self, |w| write!(w, ")")? };
                }
            }

            tee_write! {
              self, |w| {
                write!(w, " )")?;

                if arity > 0 {
                  write!(w, " )") ?
                }
              }
            }
        }

        tee_write! {
          self, |w| writeln!(w, " ) )") ?
        }

        Ok(())
    }
}

/// # Basic SMT-LIB commands using the user's parser.
impl<Parser> Solver<Parser> {
    /// Get-model command.
    pub fn get_model<Ident, Type, Value>(&mut self) -> SmtRes<Model<Ident, Type, Value>>
    where
        Parser: for<'p> IdentParser<Ident, Type, &'p mut RSmtParser>
            + for<'p> ModelParser<Ident, Type, Value, &'p mut RSmtParser>,
    {
        self.print_get_model()?;
        self.parse_get_model()
    }

    /// Get-model command when all the symbols are nullary.
    pub fn get_model_const<Ident, Type, Value>(&mut self) -> SmtRes<Vec<(Ident, Type, Value)>>
    where
        Parser: for<'p> IdentParser<Ident, Type, &'p mut RSmtParser>
            + for<'p> ModelParser<Ident, Type, Value, &'p mut RSmtParser>,
    {
        self.print_get_model()?;
        self.parse_get_model_const()
    }

    /// Get-values command.
    ///
    /// Notice that the input expression type and the output one have no reason
    /// to be the same.
    pub fn get_values<Exprs, PExpr, PValue>(&mut self, exprs: Exprs) -> SmtRes<Vec<(PExpr, PValue)>>
    where
        Parser: for<'p> ExprParser<PExpr, (), &'p mut RSmtParser>
            + for<'p> ValueParser<PValue, &'p mut RSmtParser>,
        Exprs: IntoIterator,
        Exprs::Item: Expr2Smt,
    {
        self.get_values_with(exprs, ())
            .map_err(|e| self.conf.enrich_get_values_error(e))
    }

    /// Get-values command.
    ///
    /// Notice that the input expression type and the output one have no reason to be the same.
    fn get_values_with<Exprs, PExpr, PValue, Info>(
        &mut self,
        exprs: Exprs,
        info: Info,
    ) -> SmtRes<Vec<(PExpr, PValue)>>
    where
        Info: Copy,
        Parser: for<'p> ExprParser<PExpr, Info, &'p mut RSmtParser>
            + for<'p> ValueParser<PValue, &'p mut RSmtParser>,
        Exprs: IntoIterator,
        Exprs::Item: Expr2Smt<Info>,
    {
        self.print_get_values_with(exprs, info)?;
        self.parse_get_values_with(info)
    }

    /// Get-unsat-core command.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rsmt2::Solver;
    ///
    /// let mut solver = Solver::default_z3(()).unwrap();
    ///
    /// solver.declare_const("x", "Int").unwrap();
    /// solver.declare_const("y", "Int").unwrap();
    ///
    /// solver.assert("(= (+ x y) 0)").unwrap();
    ///
    /// let future = solver.print_check_sat().unwrap();
    /// // Do stuff while the solver works.
    /// let sat = solver.parse_check_sat(future).unwrap();
    /// assert!(sat);
    /// ```
    pub fn get_unsat_core<Sym>(&mut self) -> SmtRes<Vec<Sym>>
    where
        Parser: for<'p> SymParser<Sym, &'p mut RSmtParser>,
    {
        self.print_get_unsat_core()?;
        self.parse_get_unsat_core()
    }

    /// Get-interpolant command.
    pub fn get_interpolant<Expr>(
        &mut self,
        sym_1: impl Sym2Smt,
        sym_2: impl Sym2Smt,
    ) -> SmtRes<Expr>
    where
        Parser: for<'p> ExprParser<Expr, (), &'p mut RSmtParser>,
    {
        self.get_interpolant_with(sym_1, sym_2, ())
    }

    /// Get-interpolant command.
    pub fn get_interpolant_with<Info, Expr>(
        &mut self,
        sym_1: impl Sym2Smt,
        sym_2: impl Sym2Smt,
        info: Info,
    ) -> SmtRes<Expr>
    where
        Parser: for<'p> ExprParser<Expr, Info, &'p mut RSmtParser>,
    {
        self.print_get_interpolant(sym_1, sym_2)?;
        self.parse_get_interpolant(info)
    }
}

/// # Actlit-Related Functions.
///
/// See the [`actlit` module][crate::actlit] for more details.
impl<Parser> Solver<Parser> {
    /// True if no actlits have been created since the last reset.
    ///
    /// See the [`actlit` module][crate::actlit] for more details.
    #[inline]
    fn has_actlits(&self) -> bool {
        self.actlit > 0
    }

    /// Introduces a new actlit.
    ///
    /// See the [`actlit` module][crate::actlit] for more details.
    #[inline]
    pub fn get_actlit(&mut self) -> SmtRes<crate::actlit::Actlit> {
        let id = self.actlit;
        self.actlit += 1;
        let next_actlit = crate::actlit::Actlit::new(id);
        tee_write! {
          self, |w|
            write!(w, "(declare-fun ")?;
            next_actlit.write(w)?;
            writeln!(w, " () Bool)")?
        }
        Ok(next_actlit)
    }

    /// Deactivates an activation literal, alias for `solver.set_actlit(actlit, false)`.
    ///
    /// See the [`actlit` module][crate::actlit] for more details.
    #[inline]
    pub fn de_actlit(&mut self, actlit: Actlit) -> SmtRes<()> {
        self.set_actlit(actlit, false)
    }

    /// Forces the value of an actlit and consumes it.
    ///
    /// See the [`actlit` module][crate::actlit] for more details.
    #[inline]
    pub fn set_actlit(&mut self, actlit: Actlit, b: bool) -> SmtRes<()> {
        tee_write! {
          self, |w| {
            if b {
              write!(w, "(assert ") ?
            } else {
              write!(w, "(assert (not ") ?
            }
            actlit.write(w)?;
            if b {
              writeln!(w, ")") ?
            } else {
              writeln!(w, ") )") ?
            }
          }
        }
        ::std::mem::drop(actlit);
        Ok(())
    }

    /// Asserts an expression without print information, guarded by an activation literal.
    ///
    /// See the [`actlit` module][crate::actlit] for more details.
    #[inline]
    pub fn assert_act(&mut self, actlit: &Actlit, expr: impl Expr2Smt) -> SmtRes<()> {
        self.assert_act_with(actlit, expr, ())
    }

    /// Check-sat command with activation literals, turns `unknown` results into
    /// errors.
    pub fn check_sat_act<Actlits>(&mut self, actlits: Actlits) -> SmtRes<bool>
    where
        Actlits: IntoIterator,
        Actlits::Item: Sym2Smt,
    {
        let future = self.print_check_sat_act(actlits)?;
        self.parse_check_sat(future)
    }

    /// Check-sat command with activation literals, turns `unknown` results in
    /// `None`.
    pub fn check_sat_act_or_unk<Actlits>(&mut self, actlits: Actlits) -> SmtRes<Option<bool>>
    where
        Actlits: IntoIterator,
        Actlits::Item: Sym2Smt,
    {
        let future = self.print_check_sat_act(actlits)?;
        self.parse_check_sat_or_unk(future)
    }
}

/// # SMT-LIB asynchronous commands.
impl<Parser> Solver<Parser> {
    /// Prints a check-sat command.
    ///
    /// Allows to print the `check-sat` and get the result later, *e.g.* with
    /// [`Self::parse_check_sat`].
    ///
    /// See also
    ///
    /// - [`NamedExpr`]: a convenient wrapper around any expression that gives it a name.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rsmt2::prelude::*;
    /// let mut conf = SmtConf::default_z3();
    /// conf.unsat_cores();
    /// # println!("unsat_cores: {}", conf.get_unsat_cores());
    ///
    /// let mut solver = Solver::new(conf, ()).unwrap();
    /// solver.declare_const("n", "Int").unwrap();
    /// solver.declare_const("m", "Int").unwrap();
    ///
    /// solver.assert("true").unwrap();
    ///
    /// let e_1 = "(> n 7)";
    /// let label_e_1 = "e_1";
    /// let named = NamedExpr::new(label_e_1, e_1);
    /// solver.assert(&named).unwrap();
    ///
    /// let e_2 = "(> m 0)";
    /// let label_e_2 = "e_2";
    /// let named = NamedExpr::new(label_e_2, e_2);
    /// solver.assert(&named).unwrap();
    ///
    /// let e_3 = "(< n 3)";
    /// let label_e_3 = "e_3";
    /// let named = NamedExpr::new(label_e_3, e_3);
    /// solver.assert(&named).unwrap();
    ///
    /// assert!(!solver.check_sat().unwrap());
    /// let core: Vec<String> = solver.get_unsat_core().unwrap();
    /// assert_eq!(core, vec![label_e_1, label_e_3]);
    /// ```
    #[inline]
    pub fn print_check_sat(&mut self) -> SmtRes<FutureCheckSat> {
        tee_write! {
          self, |w| write_str(w, "(check-sat)\n") ?
        }
        Ok(future_check_sat())
    }

    /// Check-sat command, with actlits.
    ///
    /// See the [`actlit` module][crate::actlit] for more details.
    #[inline]
    pub fn print_check_sat_act<Actlits>(&mut self, actlits: Actlits) -> SmtRes<FutureCheckSat>
    where
        Actlits: IntoIterator,
        Actlits::Item: Sym2Smt,
    {
        match self.conf.get_check_sat_assuming() {
            Some(ref cmd) => {
                tee_write! {
                  self, |w| write!(w, "({} (", cmd) ?
                }
                for actlit in actlits {
                    tee_write! {
                      self, |w| {
                        write!(w, " ")?;
                        actlit.sym_to_smt2(w, ()) ?
                      }
                    }
                }
                tee_write! {
                  self, |w| write_str(w, ") )\n") ?
                }
                Ok(future_check_sat())
            }
            None => {
                let msg = format!("{} does not support check-sat-assuming", self.conf.desc());
                Err(msg.into())
            }
        }
    }

    /// Parse the result of a check-sat, turns `unknown` results into errors.
    #[inline]
    pub fn parse_check_sat(&mut self, _: FutureCheckSat) -> SmtRes<bool> {
        if let Some(res) = self.smt_parser.check_sat()? {
            Ok(res)
        } else {
            Err(ErrorKind::Unknown.into())
        }
    }

    /// Parse the result of a check-sat, turns `unknown` results into `None`.
    #[inline]
    pub fn parse_check_sat_or_unk(&mut self, _: FutureCheckSat) -> SmtRes<Option<bool>> {
        self.smt_parser.check_sat()
    }

    /// Get-interpolant command.
    ///
    /// At the time of writing, only Z3 supports this command.
    #[inline]
    pub fn print_get_interpolant(
        &mut self,
        sym_1: impl Sym2Smt<()>,
        sym_2: impl Sym2Smt<()>,
    ) -> SmtRes<()> {
        tee_write! {
            self, |w|
                write_str(w, "(get-interpolant ")?;
                sym_1.sym_to_smt2(w, ())?;
                write_str(w, " ")?;
                sym_2.sym_to_smt2(w, ())?;
                write_str(w, ")\n")?
        }
        Ok(())
    }

    /// Get-model command.
    #[inline]
    fn print_get_model(&mut self) -> SmtRes<()> {
        tee_write! {
          self, |w| write_str(w, "(get-model)\n") ?
        }
        Ok(())
    }

    /// Get-assertions command.
    #[allow(dead_code)]
    fn print_get_assertions(&mut self) -> SmtRes<()> {
        tee_write! {
          self, |w| write_str(w, "(get-assertions)\n") ?
        }
        Ok(())
    }
    /// Get-assignment command.
    #[allow(dead_code)]
    fn print_get_assignment(&mut self) -> SmtRes<()> {
        tee_write! {
          self, |w| write_str(w, "(get-assignment)\n") ?
        }
        Ok(())
    }
    /// Get-unsat-assumptions command.
    #[allow(dead_code)]
    fn print_get_unsat_assumptions(&mut self) -> SmtRes<()> {
        tee_write! {
          self, |w| write_str(w, "(get-unsat-assumptions)\n") ?
        }
        Ok(())
    }
    /// Get-proof command.
    #[allow(dead_code)]
    fn print_get_proof(&mut self) -> SmtRes<()> {
        tee_write! {
          self, |w| write_str(w, "(get-proof)\n") ?
        }
        Ok(())
    }
    /// Get-unsat-core command.
    #[allow(dead_code)]
    fn print_get_unsat_core(&mut self) -> SmtRes<()> {
        tee_write! {
          self, |w| write_str(w, "(get-unsat-core)\n") ?
        }
        Ok(())
    }

    /// Get-values command.
    fn print_get_values_with<Exprs, Info>(&mut self, exprs: Exprs, info: Info) -> SmtRes<()>
    where
        Info: Copy,
        Exprs: IntoIterator,
        Exprs::Item: Expr2Smt<Info>,
    {
        tee_write! {
          self, |w| write!(w, "(get-value (") ?
        }
        for e in exprs {
            tee_write! {
              self, |w| {
                write_str(w, "\n  ")?;
                e.expr_to_smt2(w, info) ?
              }
            }
        }
        tee_write! {
          self, |w| write_str(w, "\n) )\n") ?
        }
        Ok(())
    }

    /// Check-sat with assumptions command with unit info.
    pub fn print_check_sat_assuming<Idents>(&mut self, bool_vars: Idents) -> SmtRes<FutureCheckSat>
    where
        Idents: IntoIterator,
        Idents::Item: Sym2Smt,
    {
        self.print_check_sat_assuming_with(bool_vars, ())
    }

    /// Check-sat with assumptions command.
    pub fn print_check_sat_assuming_with<Idents, Info>(
        &mut self,
        bool_vars: Idents,
        info: Info,
    ) -> SmtRes<FutureCheckSat>
    where
        Info: Copy,
        Idents: IntoIterator,
        Idents::Item: Sym2Smt<Info>,
    {
        match self.conf.get_check_sat_assuming() {
            Some(ref cmd) => {
                tee_write! {
                  self, |w| write!(w, "({} (\n ", cmd) ?
                }
                for sym in bool_vars {
                    tee_write! {
                      self, |w| {
                        write_str(w, "  ")?;
                        sym.sym_to_smt2(w, info) ?
                      }
                    }
                }
                tee_write! {
                  self, |w| write_str(w, "\n))\n") ?
                }
                Ok(future_check_sat())
            }
            None => {
                let msg = format!("{} does not support check-sat-assuming", self.conf.desc());
                Err(msg.into())
            }
        }
    }

    /// Parse the result of a `get-model`.
    fn parse_get_model<Ident, Type, Value>(&mut self) -> SmtRes<Model<Ident, Type, Value>>
    where
        Parser: for<'p> IdentParser<Ident, Type, &'p mut RSmtParser>
            + for<'p> ModelParser<Ident, Type, Value, &'p mut RSmtParser>,
    {
        let has_actlits = self.has_actlits();
        let res = self.smt_parser.get_model(has_actlits, self.parser);
        if res.is_err() && !self.conf.get_models() {
            res.chain_err(|| {
                "\
                 Note: model production is not active \
                 for this SmtConf (`conf.models()`)\
                 "
            })
        } else {
            res
        }
    }

    /// Parses the result of a `get-unsat-core`.
    fn parse_get_unsat_core<Sym>(&mut self) -> SmtRes<Vec<Sym>>
    where
        Parser: for<'p> SymParser<Sym, &'p mut RSmtParser>,
    {
        self.smt_parser.get_unsat_core(self.parser)
    }

    /// Parse the result of a `get-model` where all the symbols are nullary.
    fn parse_get_model_const<Ident, Type, Value>(&mut self) -> SmtRes<Vec<(Ident, Type, Value)>>
    where
        Parser: for<'p> IdentParser<Ident, Type, &'p mut RSmtParser>
            + for<'p> ModelParser<Ident, Type, Value, &'p mut RSmtParser>,
    {
        let has_actlits = self.has_actlits();
        let res = self.smt_parser.get_model_const(has_actlits, self.parser);
        if res.is_err() && !self.conf.get_models() {
            res.chain_err(|| {
                "\
                 Note: model production is not active \
                 for this SmtConf (`conf.models()`)\
                 "
            })
        } else {
            res
        }
    }

    /// Parse the result of a get-values.
    fn parse_get_values_with<Info, Expr, Val>(&mut self, info: Info) -> SmtRes<Vec<(Expr, Val)>>
    where
        Info: Copy,
        Parser: for<'p> ExprParser<Expr, Info, &'p mut RSmtParser>
            + for<'p> ValueParser<Val, &'p mut RSmtParser>,
    {
        let res = self.smt_parser.get_values(self.parser, info);
        if res.is_err() && !self.conf.get_models() {
            res.chain_err(|| {
                "Note: model production is not active \
                for this SmtConf (`conf.models()`)"
            })
        } else {
            res
        }
    }

    /// Parses the result of a `get-interpolant`.
    fn parse_get_interpolant<Expr, Info>(&mut self, info: Info) -> SmtRes<Expr>
    where
        Parser: for<'p> ExprParser<Expr, Info, &'p mut RSmtParser>,
    {
        let mut res = self.smt_parser.get_interpolant(self.parser, info);
        if res.is_err() {
            if !self.conf.style().is_z3() {
                res = res.chain_err(|| {
                    format!(
                        "`{}` does not support interpolant production, only Z3 does",
                        self.conf.style()
                    )
                })
            } else if !self.conf.get_interpolants() {
                res = res.chain_err(|| format!("interpolant production is not active"))
            }
        }
        res
    }
}

/// # Non-blocking commands.
impl<Parser: Send + 'static> Solver<Parser> {
    /// Asynchronous check-sat, see the [`asynch` module][crate::asynch] for details.
    ///
    /// This function is not `unsafe` in the sense that it **cannot** create undefined behavior.
    /// However, it is *unsafe* because the asynchronous check might end up running forever in the
    /// background, burning 100% CPU.
    pub unsafe fn async_check_sat_or_unk(&mut self) -> crate::asynch::CheckSatFuture<Parser> {
        crate::asynch::CheckSatFuture::new(self)
    }
}

/// # Sort-related SMT-LIB commands.
impl<Parser> Solver<Parser> {
    /// Declares a new sort.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rsmt2::Solver;
    /// let mut solver = Solver::default_z3(()).unwrap();
    /// solver.declare_sort("A", 0).unwrap();
    /// solver.declare_const("x", "A").unwrap();
    /// solver.declare_const("y", "A").unwrap();
    /// solver.declare_fun("f", & [ "A" ], "A").unwrap();
    /// solver.assert("(= (f (f x)) x)").unwrap();
    /// solver.assert("(= (f x) y)").unwrap();
    /// solver.assert("(not (= x y))").unwrap();
    /// let sat = solver.check_sat().unwrap();
    /// ```
    #[inline]
    pub fn declare_sort(&mut self, sort: impl Sort2Smt, arity: u8) -> SmtRes<()> {
        tee_write! {
          self, |w| {
            write_str(w, "(declare-sort ")?;
            sort.sort_to_smt2(w)?;
            writeln!(w, " {})", arity) ?
          }
        }
        Ok(())
    }

    /// Defines a new sort.
    ///
    /// # Examples
    ///
    /// Note the use of [`Self::define_null_sort`] to avoid problems with empty arguments.
    ///
    /// ```rust
    /// # use rsmt2::Solver;
    /// let mut solver = Solver::default_z3(()).unwrap();
    /// solver.define_sort("MySet", & ["T"], "(Array T Bool)").unwrap();
    /// solver.define_null_sort("IList", "(List Int)").unwrap();
    /// solver.define_sort(
    ///     "List-Set", & ["T"], "(Array (List T) Bool)"
    /// ).unwrap();
    /// solver.define_null_sort("I", "Int").unwrap();
    ///
    /// solver.declare_const("s1", "(MySet I)").unwrap();
    /// solver.declare_const("s2", "(List-Set Int)").unwrap();
    /// solver.declare_const("a", "I").unwrap();
    /// solver.declare_const("l", "IList").unwrap();
    ///
    /// solver.assert("(= (select s1 a) true)").unwrap();
    /// solver.assert("(= (select s2 l) false)").unwrap();
    /// let sat = solver.check_sat().unwrap();
    /// ```
    #[inline]
    pub fn define_sort<Args>(
        &mut self,
        sort_sym: impl Sym2Smt,
        args: Args,
        body: impl Sort2Smt,
    ) -> SmtRes<()>
    where
        Args: IntoIterator,
        Args::Item: Sort2Smt,
    {
        tee_write! {
          self, |w| {
            write_str(w, "( define-sort ")?;
            sort_sym.sym_to_smt2(w, ())?;
            write_str(w, "\n   ( ")?;
          }
        }
        for arg in args {
            tee_write! {
              self, |w| {
                arg.sort_to_smt2(w)?;
                write_str(w, " ") ?
              }
            }
        }
        tee_write! {
          self, |w| {
            write_str(w, ")\n   ")?;
            body.sort_to_smt2(w)?;
            write_str(w, "\n)\n") ?
          }
        }
        Ok(())
    }

    /// Defines a new nullary sort.
    ///
    /// When using [`Self::define_sort`] with empty `args`, rust complains because it does not know
    /// what the `Arg` type parameter is. This function addresses this problem by not having
    /// arguments.
    #[inline]
    pub fn define_null_sort(&mut self, sym: impl Sym2Smt, body: impl Sort2Smt) -> SmtRes<()> {
        // Does not matter, just needs to implement `Sort2Smt`
        //                                                vvvv
        self.define_sort(sym, None as Option<&str>, body)
    }
}

/// # SMT-LIB commands vehiculating user information.
impl<Parser> Solver<Parser> {
    /// Declares a new constant.
    #[inline]
    pub fn declare_const_with<Info>(
        &mut self,
        symbol: impl Sym2Smt<Info>,
        out_sort: impl Sort2Smt,
        info: Info,
    ) -> SmtRes<()>
    where
        Info: Copy,
    {
        tee_write! {
          self, |w| {
            write_str(w, "(declare-const ")?;
            symbol.sym_to_smt2(w, info)?;
            write_str(w, " ")?;
            out_sort.sort_to_smt2(w)?;
            write_str(w, ")\n") ?
          }
        }
        Ok(())
    }

    /// Declares a new function symbol.
    #[inline]
    pub fn declare_fun_with<Args, Info>(
        &mut self,
        symbol: impl Sym2Smt<Info>,
        args: Args,
        out: impl Sort2Smt,
        info: Info,
    ) -> SmtRes<()>
    where
        Info: Copy,
        Args: IntoIterator,
        Args::Item: Sort2Smt,
    {
        tee_write! {
          self, |w| {
            write_str(w, "(declare-fun ")?;
            symbol.sym_to_smt2(w, info)?;
            write_str(w, " ( ") ?
          }
        }
        for arg in args {
            tee_write! {
              self, |w| {
                arg.sort_to_smt2(w)?;
                write_str(w, " ") ?
              }
            }
        }
        tee_write! {
          self, |w| {
            write_str(w, ") ")?;
            out.sort_to_smt2(w)?;
            write_str(w, ")\n") ?
          }
        }
        Ok(())
    }

    /// Defines a new constant.
    #[inline]
    pub fn define_const_with<Info>(
        &mut self,
        symbol: impl Sym2Smt<Info>,
        out_sort: impl Sort2Smt,
        body: impl Expr2Smt<Info>,
        info: Info,
    ) -> SmtRes<()>
    where
        Info: Copy,
    {
        tee_write! {
          self, |w| {
            write_str(w, "(define-const ")?;
            symbol.sym_to_smt2(w, info)?;
            write_str(w, " ")?;
            out_sort.sort_to_smt2(w)?;
            write_str(w, " ")?;
            body.expr_to_smt2(w, info)?;
            write_str(w, ")\n") ?
          }
        }
        Ok(())
    }

    /// Defines a new function symbol.
    #[inline]
    pub fn define_fun_with<Args, Info>(
        &mut self,
        symbol: impl Sym2Smt<Info>,
        args: Args,
        out: impl Sort2Smt,
        body: impl Expr2Smt<Info>,
        info: Info,
    ) -> SmtRes<()>
    where
        Info: Copy,
        Args: IntoIterator,
        Args::Item: SymAndSort<Info>,
    {
        tee_write! {
          self, |w| {
            write_str(w, "(define-fun ")?;
            symbol.sym_to_smt2(w, info)?;
            write_str(w, " ( ") ?
          }
        }
        for arg in args {
            let sym = arg.sym();
            let sort = arg.sort();
            tee_write! {
              self, |w| {
                write_str(w, "(")?;
                sym.sym_to_smt2(w, info)?;
                write_str(w, " ")?;
                sort.sort_to_smt2(w)?;
                write_str(w, ") ") ?
              }
            }
        }
        tee_write! {
          self, |w| {
            write_str(w, ") ")?;
            out.sort_to_smt2(w)?;
            write_str(w, "\n   ")?;
            body.expr_to_smt2(w, info)?;
            write_str(w, "\n)\n") ?
          }
        }
        Ok(())
    }

    /// Defines some new (possibily mutually) recursive functions.
    pub fn define_funs_rec_with<Defs, Info>(&mut self, funs: Defs, info: Info) -> SmtRes<()>
    where
        Info: Copy,
        Defs: IntoIterator + Clone,
        Defs::Item: FunDef<Info>,
    {
        // Header.
        tee_write! {
          self, |w| write_str(w, "(define-funs-rec (\n") ?
        }

        // Signatures.
        for fun in funs.clone() {
            let sym = fun.fun_sym();
            let args = fun.args();
            let out = fun.out_sort();

            tee_write! {
                self, |w| {
                    write_str(w, "   (")?;
                    sym.sym_to_smt2(w, info)?;
                    write_str(w, " ( ") ?
                }
            }

            for arg in args {
                tee_write! {
                    self, |w| {
                        let sym = arg.sym();
                        let sort = arg.sort();
                        write_str(w, "(")?;
                        sym.sym_to_smt2(w, info)?;
                        write_str(w, " ")?;
                        sort.sort_to_smt2(w)?;
                        write_str(w, ") ") ?
                    }
                }
            }

            tee_write! {
              self, |w| {
                write_str(w, ") ")?;
                out.sort_to_smt2(w)?;
                write_str(w, ")\n") ?
              }
            }
        }
        tee_write! {
          self, |w| write_str(w, " ) (") ?
        }

        // Bodies
        for fun in funs {
            let body = fun.body();
            tee_write! {
              self, |w| {
                write_str(w, "\n   ")?;
                body.expr_to_smt2(w, info) ?
              }
            }
        }
        tee_write! {
          self, |w| write_str(w, "\n )\n)\n") ?
        }
        Ok(())
    }

    /// Defines a new recursive function.
    #[inline]
    pub fn define_fun_rec_with<Args, Info>(
        &mut self,
        symbol: impl Sym2Smt<Info>,
        args: Args,
        out: impl Sort2Smt,
        body: impl Expr2Smt<Info>,
        info: Info,
    ) -> SmtRes<()>
    where
        Info: Copy,
        Args: IntoIterator,
        Args::Item: SymAndSort<Info>,
    {
        // Header.
        tee_write! {
          self, |w| write_str(w, "(define-fun-rec (\n") ?
        }

        tee_write! {
          self, |w| {
            // Signature.
            write_str(w, "   (")?;
            symbol.sym_to_smt2(w, info)?;
            write_str(w, " ( ") ?
          }
        }

        for arg in args {
            let sym = arg.sym();
            let sort = arg.sort();
            tee_write! {
              self, |w| {
                write_str(w, "(")?;
                sym.sym_to_smt2(w, info)?;
                write_str(w, " ")?;
                sort.sort_to_smt2(w)?;
                write_str(w, ") ") ?
              }
            }
        }

        tee_write! {
          self, |w| {
            write_str(w, ") ")?;
            out.sort_to_smt2(w)?;
            write_str(w, ")\n")?;
            write_str(w, " ) (")?;

            // Body.
            write_str(w, "\n   ")?;
            body.expr_to_smt2(w, info)?;
            write_str(w, "\n )\n)\n") ?
          }
        }
        Ok(())
    }

    /// Asserts an expression with info, optional actlit and optional name.
    #[inline]
    pub fn full_assert<Act, Name, Info>(
        &mut self,
        actlit: Option<Act>,
        name: Option<Name>,
        expr: impl Expr2Smt<Info>,
        info: Info,
    ) -> SmtRes<()>
    where
        Info: Copy,
        Name: Sym2Smt,
        Act: Sym2Smt,
    {
        tee_write! {
            self, |w| {
                write_str(w, "(assert")?;
                if name.is_some() {
                    write_str(w, " (!")?;
                }
                if let Some(actlit) = actlit.as_ref() {
                    write_str(w, " (=> ")?;
                    actlit.sym_to_smt2(w, ())?;
                }
                write_str(w, "\n    ")?;
                expr.expr_to_smt2(w, info)?;
                write_str(w, "\n")?;
                if actlit.is_some() {
                    write_str(w, ")")?;
                }
                if let Some(name) = name.as_ref() {
                    write_str(w, " :named ")?;
                    name.sym_to_smt2(w, ())?;
                    write_str(w, ")")?;
                }
                write_str(w, ")\n")?;
            }
        }
        Ok(())
    }

    /// Asserts an expression with an activation literal, a name and some print info.
    #[inline]
    pub fn named_assert_act_with<Info>(
        &mut self,
        actlit: &Actlit,
        name: impl Sym2Smt,
        expr: impl Expr2Smt<Info>,
        info: Info,
    ) -> SmtRes<()>
    where
        Info: Copy,
    {
        self.full_assert(Some(actlit), Some(name), expr, info)
    }

    /// Asserts an expression with some print information, guarded by an activation literal.
    ///
    /// See the [`actlit` module][crate::actlit] for more details.
    #[inline]
    pub fn assert_act_with<Info>(
        &mut self,
        actlit: &Actlit,
        expr: impl Expr2Smt<Info>,
        info: Info,
    ) -> SmtRes<()>
    where
        Info: Copy,
    {
        let name: Option<&str> = None;
        self.full_assert(Some(actlit.as_ref()), name, expr, info)
    }

    /// Asserts an expression with some print information.
    #[inline]
    pub fn assert_with<Info, Expr>(&mut self, expr: Expr, info: Info) -> SmtRes<()>
    where
        Info: Copy,
        Expr: Expr2Smt<Info>,
    {
        let name: Option<&str> = None;
        let act: Option<Actlit> = None;
        self.full_assert(act, name, expr, info)
    }

    /// Asserts a named expression.
    #[inline]
    pub fn named_assert<Expr, Name>(&mut self, name: Name, expr: Expr) -> SmtRes<()>
    where
        Name: Sym2Smt,
        Expr: Expr2Smt,
    {
        let act: Option<Actlit> = None;
        self.full_assert(act, Some(name), expr, ())
    }

    /// Asserts an expression with a name and some print info.
    #[inline]
    pub fn named_assert_with<Name, Info, Expr>(
        &mut self,
        name: Name,
        expr: Expr,
        info: Info,
    ) -> SmtRes<()>
    where
        Info: Copy,
        Expr: Expr2Smt<Info>,
        Name: Sym2Smt,
    {
        let act: Option<Actlit> = None;
        self.full_assert(act, Some(name), expr, info)
    }

    /// Check-sat assuming command, turns `unknown` results into errors.
    pub fn check_sat_assuming_with<Info, Syms>(&mut self, idents: Syms, info: Info) -> SmtRes<bool>
    where
        Info: Copy,
        Syms: IntoIterator,
        Syms::Item: Sym2Smt<Info>,
    {
        let future = self.print_check_sat_assuming_with(idents, info)?;
        self.parse_check_sat(future)
    }

    /// Check-sat assuming command, turns `unknown` results into `None`.
    pub fn check_sat_assuming_or_unk_with<Idents, Info>(
        &mut self,
        idents: Idents,
        info: Info,
    ) -> SmtRes<Option<bool>>
    where
        Info: Copy,
        Idents: IntoIterator,
        Idents::Item: Sym2Smt<Info>,
    {
        let future = self.print_check_sat_assuming_with(idents, info)?;
        self.parse_check_sat_or_unk(future)
    }
}

/// # Other commands.
impl<Parser> Solver<Parser> {
    /// Set option command.
    #[inline]
    pub fn set_option<Value: ::std::fmt::Display>(
        &mut self,
        option: &str,
        value: Value,
    ) -> SmtRes<()> {
        match option {
            ":interactive_mode" => return Err("illegal set-option on interactive mode".into()),
            ":print_success" => {
                return Err("illegal set-option on print success, \
                            use `SmtConf` to activate it"
                    .into())
            }
            _ => (),
        };
        tee_write! {
          self, |w| writeln!(
            w, "(set-option {} {})", option, value
          ) ?
        }
        Ok(())
    }

    /// Activates unsat core production.
    #[inline]
    pub fn produce_unsat_cores(&mut self) -> SmtRes<()> {
        self.set_option(":produce-unsat-cores", "true")
    }
    /// Activates model production.
    #[inline]
    pub fn produce_models(&mut self) -> SmtRes<()> {
        self.set_option(":produce-models", "true")
    }

    /// Resets the assertions in the solver.
    #[inline]
    pub fn reset_assertions(&mut self) -> SmtRes<()> {
        tee_write! {
          self, |w| write_str(w, "(reset-assertions)\n") ?
        }
        Ok(())
    }

    // // |===| Inspecting settings.

    /// Get info command.
    #[inline]
    pub fn get_info(&mut self, flag: &str) -> SmtRes<()> {
        tee_write! {
          self, |w| writeln!(w, "(get-info {})", flag) ?
        }
        Ok(())
    }
    /// Get option command.
    #[inline]
    pub fn get_option(&mut self, option: &str) -> SmtRes<()> {
        tee_write! {
          self, |w| writeln!(w, "(get-option {})", option) ?
        }
        Ok(())
    }

    // |===| Script information.

    /// Set info command.
    #[inline]
    pub fn set_info(&mut self, attribute: &str) -> SmtRes<()> {
        tee_write! {
          self, |w| writeln!(w, "(set-info {})", attribute) ?
        }
        Ok(())
    }
    /// Echo command.
    #[inline]
    pub fn echo(&mut self, text: &str) -> SmtRes<()> {
        tee_write! {
          self, |w| writeln!(w, "(echo \"{}\")", text) ?
        }
        Ok(())
    }
}
