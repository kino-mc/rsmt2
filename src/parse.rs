/*! SMT Lib 2 result parsers. */

use std::str ;

use nom::multispace ;

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

named!{ pub open_paren<()>,
  map!( preceded!( opt!(multispace), char!('(')), |_| () )
}

pub type OpenParen = SmtRes<()> ;

named!{ pub unexp_or_open_paren<OpenParen>,
  alt!(
    map!( unexpected, |e| Err(e) ) |
    map!( open_paren, |_| Ok(()) )
  )
}

named!{ pub close_paren<()>,
  map!( preceded!( opt!(multispace), char!(')') ), |_| () )
}


named!{ pub define_fun,
  delimited!( opt!(multispace), tag!("define-fun"), opt!(multispace) )
}