#![ doc = "

A wrapper around the z3 SMT solver.

"]

pub mod common ;
pub mod solver_traits ;
pub mod driver ;
pub mod solver ;

pub type Solver = solver::Solver ;