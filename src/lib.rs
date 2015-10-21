/*! A wrapper around an SMT Lib 2(.5)-compliant SMT solver.

# To do

* Cleaner error handling in solver commands (see `check_sat_assuming`).
* Add `inline` to many (probably not all) of the commands in solver.
*/

#[macro_use]
extern crate nom ;

use nom::ReadProducer ;

pub mod common ;
pub mod conf ;
pub mod parse ;
pub mod solver ;