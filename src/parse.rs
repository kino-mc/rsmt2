/*! SMT Lib 2 result parsers. */

use std::str ;

use nom::{ multispace, IResult } ;

use common::{ UnexSmtRes, SmtRes } ;
use common::UnexSmtRes::* ;


named!{ pub unsupported<UnexSmtRes>,
  map!( tag!("unsupported"), |_| Unsupported )
}

named!{ pub error<UnexSmtRes>,
  chain!(
    char!('(') ~
    opt!(multispace) ~
    tag!("error") ~
    multispace ~
    char!('"') ~
    msg: is_not!( "\"" ) ~
    char!('"') ~
    opt!(multispace) ~
    char!(')'),
    || Error(str::from_utf8(msg).unwrap().to_string())
  )
}

named!{ pub unexpected<UnexSmtRes>, alt!( unsupported | error ) }


pub type SuccessRes = SmtRes<()> ;

named!{ pub success<SuccessRes>,
  alt!(
    map!( tag!("success"), |_| Ok(()) ) |
    map!( unexpected, |e| Err(e) )
  )
}


pub type CheckSatRes = SmtRes<bool> ;

named!{ pub check_sat<CheckSatRes>,
  alt!(
    map!( tag!("sat"), |_| Ok(true) ) |
    map!( tag!("unsat"), |_| Ok(false) ) |
    map!( unexpected, |e| Err(e) )
  )
}