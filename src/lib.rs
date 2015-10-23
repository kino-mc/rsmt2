/*! A wrapper around an SMT Lib 2(.5)-compliant SMT solver.

# To do

* cleaner error handling in solver commands (see `check_sat_assuming`)
* add `inline` to many (probably not all) of the commands in solver
* update `nom` to remove the hack on `Stepper` for child processes
*/

#[macro_use]
extern crate nom ;

pub mod common ;
pub mod conf ;
pub mod parse ;
pub mod solver ;