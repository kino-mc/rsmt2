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

* update `nom` to remove the hack on `Stepper` for child processes
*/

#[macro_use]
extern crate nom ;

mod common ;
mod conf ;
mod parse ;
mod solver ;

pub use common::* ;
pub use conf::* ;
pub use solver::* ;