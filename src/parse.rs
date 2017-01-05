// Copyright 2015 Adrien Champion. See the COPYRIGHT file at the top-level
// directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! SMT Lib 2 result parsers. */

use std::str ;

use nom::{ IResult, multispace } ;

use errors::* ;


pub fn unsupported<T>(bytes: & [u8]) -> IResult<& [u8], Res<T>, u32> {
  map!(
    bytes,
    tag!("unsupported"), |_| Err( ErrorKind::Unsupported.into() )
  )
}

pub fn error<T>(bytes: & [u8]) -> IResult<& [u8], Res<T>, u32> {
  chain!(
    bytes,
    char!('(') ~
    opt!(multispace) ~
    tag!("error") ~
    multispace ~
    char!('"') ~
    msg: is_not!( "\"" ) ~
    char!('"') ~
    opt!(multispace) ~
    char!(')'),
    || match str::from_utf8(msg) {
      Ok(s) => bail!(
        ErrorKind::SolverError( s.into() )
      ),
      Err(e) => Err(e).chain_err(
        || ErrorKind::SolverError(
          "unable to convert solver error to utf8".into()
        )
      )
    }
  )
}

pub fn unexpected<T>(bytes: & [u8]) -> IResult<& [u8], Res<T>, u32> {
  alt!( bytes, unsupported | error )
}

named!{ pub success< Res<()> >,
  preceded!(
    opt!(multispace),
    alt!(
      map!( tag!("success"), |_| Ok(()) ) |
      unexpected
    )
  )
}

named!{ pub check_sat< Res<bool> >,
  preceded!(
    opt!(multispace),
    alt!(
      map!( tag!("sat"), |_| Ok(true) ) |
      map!( tag!("unsat"), |_| Ok(false) ) |
      map!( unexpected, |e| e )
    )
  )
}

// pub fn check_sat(bytes: & [u8]) -> (String, CheckSatRes) {
//   wrap!( parse_check_sat(bytes) )
// }

named!{ pub open_paren<()>,
  map!( preceded!( opt!(multispace), char!('(')), |_| () )
}

named!{ pub close_paren<()>,
  map!( preceded!( opt!(multispace), char!(')') ), |_| () )
}
