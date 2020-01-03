//! Basic types used by the library.

use std::{fmt, io};

pub use crate::errors::*;

/// Type of a model.
pub type Model<Ident, Type, Value> = Vec<(Ident, Vec<(Ident, Type)>, Type, Value)>;

/// A symbol printable in the SMT Lib 2 standard given some info.
pub trait Sym2Smt<Info> {
    /// Prints a symbol to a writer given some info.
    fn sym_to_smt2<Writer>(&self, w: &mut Writer, i: Info) -> SmtRes<()>
    where
        Writer: io::Write;
}

/// An expression printable in the SMT Lib 2 standard given some info.
pub trait Expr2Smt<Info> {
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

/// SMT Lib 2 logics.
///
/// See [`Solver::set_logic`][logic].
///
/// [logic]: struct.Solver.html#method.set_logic
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
    /** Quantifier-free arrays, uninterpreted functions, linear integer
    arithmetic. */
    QF_AUFLIA,
    /** Quantifier-free arrays, uninterpreted functions, linear integer
    arithmetic. */
    AUFLIA,
    /// Arrays, uninterpreted functions, linear integer/real arithmetic.
    AUFLIRA,
    /// arrays, uninterpreted functions, non-linear integer/real arithmetic.
    AUFNIRA,
    /// Linear real arithmetic.
    LRA,
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

#[test]
fn logic() {
    use crate::conf::SmtConf;
    use crate::Solver;

    let conf = SmtConf::z3();

    let mut solver = Solver::new(conf, ()).expect("solver");

    solver.set_logic(Logic::QF_UF).expect("QF_UF");
    solver.reset().expect("reset");
    solver.set_logic(Logic::QF_LIA).expect("QF_LIA");
    solver.reset().expect("reset");
    solver.set_logic(Logic::QF_NIA).expect("QF_NIA");
    solver.reset().expect("reset");
    solver.set_logic(Logic::QF_LRA).expect("QF_LRA");
    solver.reset().expect("reset");
    solver.set_logic(Logic::QF_AUFLIA).expect("QF_AUFLIA");
    solver.reset().expect("reset");
    solver.set_logic(Logic::AUFLIA).expect("AUFLIA");
    solver.reset().expect("reset");
    solver.set_logic(Logic::AUFLIRA).expect("AUFLIRA");
    solver.reset().expect("reset");
    solver.set_logic(Logic::AUFNIRA).expect("AUFNIRA");
    solver.reset().expect("reset");
    solver.set_logic(Logic::LRA).expect("LRA");
    solver.reset().expect("reset");
}
