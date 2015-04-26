#![ doc = "

A wrapper around the z3 SMT solver.

"]

extern crate parser_combinators as pcomb ;

pub mod common ;
pub mod conf ;
pub mod solver_traits ;
pub mod printer ;
pub mod solver ;

pub type Solver = solver::Solver ;