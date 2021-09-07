//! Basic types used by the library.

use std::{fmt, io};

pub use crate::errors::*;

/// Type of a model.
pub type Model<Ident, Type, Value> = Vec<(Ident, Vec<(Ident, Type)>, Type, Value)>;

/// A symbol printable in the SMT Lib 2 standard given some info.
pub trait Sym2Smt<Info = ()> {
    /// Prints a symbol to a writer given some info.
    fn sym_to_smt2<Writer>(&self, w: &mut Writer, i: Info) -> SmtRes<()>
    where
        Writer: io::Write;
}

/// An expression printable in the SMT Lib 2 standard given some info.
pub trait Expr2Smt<Info = ()> {
    /// Prints an expression to a writer given some info.
    fn expr_to_smt2<Writer>(&self, w: &mut Writer, i: Info) -> SmtRes<()>
    where
        Writer: io::Write;
}

/// A sort printable in the SMT Lib 2 standard.
pub trait Sort2Smt {
    /// Prints a sort to a writer info.
    fn sort_to_smt2<Writer>(&self, w: &mut Writer) -> SmtRes<()>
    where
        Writer: io::Write;
}

/// A symbol and a sort, implemented by by symbol/sort pairs.
///
/// Implement this trait if you want to use your own data structures in solver functions working on
/// lists of sorted symbols. For example,
///
/// - [Solver::define_fun][crate::Solver::define_fun],
/// - [Solver::define_funs_rec_with][crate::Solver::define_funs_rec_with].
pub trait SymAndSort<Info = ()> {
    /// Type of the symbol.
    type Sym: Sym2Smt<Info>;
    /// Type of the sort.
    type Sort: Sort2Smt;
    /// Symbol accessor.
    fn sym(&self) -> &Self::Sym;
    /// Sort accessor.
    fn sort(&self) -> &Self::Sort;
}
impl<'a, T, Info> SymAndSort<Info> for &'a T
where
    T: SymAndSort<Info>,
{
    type Sym = <T as SymAndSort<Info>>::Sym;
    type Sort = <T as SymAndSort<Info>>::Sort;
    fn sym(&self) -> &Self::Sym {
        (*self).sym()
    }
    fn sort(&self) -> &Self::Sort {
        (*self).sort()
    }
}
impl<Info, Sym, Sort> SymAndSort<Info> for (Sym, Sort)
where
    Sym: Sym2Smt<Info>,
    Sort: Sort2Smt,
{
    type Sym = Sym;
    type Sort = Sort;
    fn sym(&self) -> &Sym {
        &self.0
    }
    fn sort(&self) -> &Sort {
        &self.1
    }
}

pub trait FunDef<Info = ()> {
    type FunSym: Sym2Smt<Info>;
    type SortedSym: SymAndSort<Info>;
    type ArgsIter: Iterator<Item = Self::SortedSym>;
    type OutSort: Sort2Smt;
    type Body: Expr2Smt<Info>;

    fn fun_sym(&self) -> &Self::FunSym;

    fn args(&self) -> Self::ArgsIter;

    fn out_sort(&self) -> &Self::OutSort;

    fn body(&self) -> &Self::Body;
}
impl<'a, T, Info> FunDef<Info> for &'a T
where
    T: FunDef<Info>,
{
    type FunSym = T::FunSym;
    type SortedSym = T::SortedSym;
    type ArgsIter = T::ArgsIter;
    type OutSort = T::OutSort;
    type Body = T::Body;

    fn fun_sym(&self) -> &Self::FunSym {
        (*self).fun_sym()
    }

    fn args(&self) -> Self::ArgsIter {
        (*self).args()
    }

    fn out_sort(&self) -> &Self::OutSort {
        (*self).out_sort()
    }

    fn body(&self) -> &Self::Body {
        (*self).body()
    }
}
impl<'a, FunSym, SortedSym, ArgsIter, Args, OutSort, Body, Info> FunDef<Info>
    for (FunSym, Args, OutSort, Body)
where
    FunSym: Sym2Smt<Info>,
    SortedSym: SymAndSort<Info> + 'a,
    ArgsIter: Iterator<Item = SortedSym> + 'a,
    Args: IntoIterator<IntoIter = ArgsIter> + Clone,
    OutSort: Sort2Smt,
    Body: Expr2Smt<Info>,
{
    type FunSym = FunSym;
    type SortedSym = SortedSym;
    type ArgsIter = ArgsIter;
    type OutSort = OutSort;
    type Body = Body;

    fn fun_sym(&self) -> &FunSym {
        &self.0
    }
    fn args(&self) -> ArgsIter {
        self.1.clone().into_iter()
    }
    fn out_sort(&self) -> &OutSort {
        &self.2
    }
    fn body(&self) -> &Body {
        &self.3
    }
}

/// Writes a string.
#[inline(always)]
pub fn write_str<W: io::Write>(w: &mut W, s: &str) -> SmtRes<()> {
    w.write_all(s.as_bytes())?;
    Ok(())
}

impl<'a, T, Info> Sym2Smt<Info> for &'a T
where
    T: Sym2Smt<Info> + ?Sized,
{
    fn sym_to_smt2<Writer>(&self, writer: &mut Writer, info: Info) -> SmtRes<()>
    where
        Writer: io::Write,
    {
        (*self).sym_to_smt2(writer, info)
    }
}

impl<'a, T, Info> Expr2Smt<Info> for &'a T
where
    T: Expr2Smt<Info> + ?Sized,
{
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: Info) -> SmtRes<()>
    where
        Writer: io::Write,
    {
        (*self).expr_to_smt2(writer, info)
    }
}

impl<'a, T> Sort2Smt for &'a T
where
    T: Sort2Smt + ?Sized,
{
    fn sort_to_smt2<Writer>(&self, writer: &mut Writer) -> SmtRes<()>
    where
        Writer: io::Write,
    {
        (*self).sort_to_smt2(writer)
    }
}

impl<T> Sym2Smt<T> for str {
    fn sym_to_smt2<Writer>(&self, writer: &mut Writer, _: T) -> SmtRes<()>
    where
        Writer: io::Write,
    {
        write_str(writer, self)
    }
}
impl<T> Expr2Smt<T> for str {
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, _: T) -> SmtRes<()>
    where
        Writer: io::Write,
    {
        write_str(writer, self)
    }
}
impl Sort2Smt for str {
    fn sort_to_smt2<Writer>(&self, writer: &mut Writer) -> SmtRes<()>
    where
        Writer: io::Write,
    {
        write_str(writer, self)
    }
}

impl<T> Sym2Smt<T> for String {
    fn sym_to_smt2<Writer>(&self, writer: &mut Writer, _: T) -> SmtRes<()>
    where
        Writer: io::Write,
    {
        write_str(writer, self)
    }
}
impl<T> Expr2Smt<T> for String {
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, _: T) -> SmtRes<()>
    where
        Writer: io::Write,
    {
        write_str(writer, self)
    }
}
impl Sort2Smt for String {
    fn sort_to_smt2<Writer>(&self, writer: &mut Writer) -> SmtRes<()>
    where
        Writer: io::Write,
    {
        write_str(writer, self)
    }
}

/// Wraps an expression and a symbol. Symbol is understood as the name of the expression.
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
/// let e_2 = "(and (> m n) (< m 7))";
/// let label_e_2 = "e_2";
/// let named = NamedExpr::new(label_e_2, e_2);
/// solver.assert(&named).unwrap();
///
/// assert!(!solver.check_sat().unwrap());
/// let core: Vec<String> = solver.get_unsat_core().unwrap();
/// assert_eq!(core, vec![label_e_1, label_e_2]);
/// ```
pub struct NamedExpr<Sym, Expr> {
    /// Symbol.
    sym: Sym,
    /// Expression.
    expr: Expr,
}
impl<Sym, Expr> NamedExpr<Sym, Expr> {
    /// Constructor.
    pub fn new(sym: Sym, expr: Expr) -> Self {
        Self { sym, expr }
    }
}
impl<Sym, Expr, Info> Expr2Smt<Info> for NamedExpr<Sym, Expr>
where
    Sym: Sym2Smt<()>,
    Expr: Expr2Smt<Info>,
{
    fn expr_to_smt2<Writer>(&self, w: &mut Writer, i: Info) -> SmtRes<()>
    where
        Writer: io::Write,
    {
        write!(w, "(! ")?;
        self.expr.expr_to_smt2(w, i)?;
        write!(w, " :named ")?;
        self.sym.sym_to_smt2(w, ())?;
        write!(w, ")")?;
        Ok(())
    }
}

/// SMT Lib 2 logics, used with [`Solver::set_logic`][crate::Solver::set_logic].
#[allow(non_camel_case_types)]
#[derive(Clone, Copy)]
pub enum Logic {
    /// Quantifier-free uninterpreted functions.
    QF_UF,
    /// Quantifier-free linear integer arithmetic.
    QF_LIA,
    /// Quantifier-free non-linear integer arithmetic.
    QF_NIA,
    /// Quantifier-free linear real arithmetic.
    QF_LRA,
    /// Quantifier-free arrays, uninterpreted functions, linear integer arithmetic.
    QF_AUFLIA,
    /// Arrays, uninterpreted functions, linear integer arithmetic.
    AUFLIA,
    /// Arrays, uninterpreted functions, linear integer/real arithmetic.
    AUFLIRA,
    /// arrays, uninterpreted functions, non-linear integer/real arithmetic.
    AUFNIRA,
    /// Linear real arithmetic.
    LRA,
    /// Quantifier-free fixed-size bitvectors.
    QF_BV,
    /// Quantifier-free uninterpreted functions, fixed-size bitvectors.
    QF_UFBV,
    /// Quantifier-free arrays, fixed-size bitvectors.
    QF_ABV,
    /// Quantifier-free arrays, uninterpreted functions, fixed-size bitvectors.
    QF_AUFBV,
}
impl fmt::Display for Logic {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        use self::Logic::*;
        match *self {
            QF_UF => write!(fmt, "QF_UF"),
            QF_LIA => write!(fmt, "QF_LIA"),
            QF_NIA => write!(fmt, "QF_NIA"),
            QF_LRA => write!(fmt, "QF_LRA"),
            QF_AUFLIA => write!(fmt, "QF_AUFLIA"),
            AUFLIA => write!(fmt, "AUFLIA"),
            AUFLIRA => write!(fmt, "AUFLIRA"),
            AUFNIRA => write!(fmt, "AUFNIRA"),
            LRA => write!(fmt, "LRA"),
            QF_BV => write!(fmt, "QF_BV"),
            QF_UFBV => write!(fmt, "QF_UFBV"),
            QF_ABV => write!(fmt, "QF_ABV"),
            QF_AUFBV => write!(fmt, "QF_AUFBV"),
        }
    }
}
impl Logic {
    /// Prints the logic in a writer in SMT Lib 2 format.
    pub fn to_smt2<W: io::Write>(self, writer: &mut W, _: ()) -> SmtRes<()> {
        write!(writer, "{}", self)?;
        Ok(())
    }
}
