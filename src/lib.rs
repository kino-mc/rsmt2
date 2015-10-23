// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

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