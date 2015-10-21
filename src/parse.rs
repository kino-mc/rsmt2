/*! SMT Lib 2 result parsers. */

use std::str ;

use nom::{ multispace, IResult } ;

use common::{ UnexSmtRes, SmtRes } ;
use common::UnexSmtRes::* ;


named!{ unsupported<UnexSmtRes>,
  map!( tag!("unsupported"), |_| Unsupported )
}

named!{ error<UnexSmtRes>,
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

named!{ unexpected<UnexSmtRes>, alt!( unsupported | error ) }


pub type SuccessRes = SmtRes<()> ;

named!{ success<SuccessRes>,
  alt!(
    map!( tag!("success"), |_| Ok(()) ) |
    map!( unexpected, |e| Err(e) )
  )
}


pub type CheckSatRes = SmtRes<bool> ;

named!{ check_sat<CheckSatRes>,
  alt!(
    map!( tag!("sat"), |_| Ok(true) ) |
    map!( tag!("unsat"), |_| Ok(false) ) |
    map!( unexpected, |e| Err(e) )
  )
}