//! Basic types used by the library.

use std::{fmt, io};

use crate::prelude::*;

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
