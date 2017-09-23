// See the LICENSE files at the top-level directory of this distribution.
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
  do_parse!(
    bytes,
    char!('(') >>
    opt!(multispace) >>
    tag!("error") >>
    multispace >>
    char!('"') >>
    msg: is_not!( "\"" ) >>
    char!('"') >>
    opt!(multispace) >>
    char!(')') >> (
      match str::from_utf8(msg) {
        Ok(s) => Err(
          ErrorKind::SolverError( s.into() ).into()
        ),
        Err(e) => Err(e).chain_err(
          || ErrorKind::SolverError(
            "unable to convert solver error to utf8".into()
          )
        )
      }
    )
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

named!{ pub check_sat< Res< Option<bool> > >,
  preceded!(
    opt!(multispace),
    alt!(
      map!( tag!("sat"), |_| Ok( Some(true) ) ) |
      map!( tag!("unsat"), |_| Ok( Some(false) ) ) |
      map!( tag!("unknown"), |_| Ok( None ) ) |
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


// /// SMT-LIB 2.0 parser.
// pub struct SmtParser<'a> {
//   /// Text being parsed.
//   string: & 'a str,
//   /// Current position in the text.
//   cursor: usize,
//   /// Stack of positions, for backtracking.
//   stack: Vec<usize>,
// }
// impl<'a> SmtParser<'a> {
//   /// Constructor.
//   pub fn new(string: & 'a str) -> Self {
//     SmtParser { string, cursor: 0, stack: Vec::with_capacity(3) }
//   }

//   /// Parses whitespaces or comments.
//   pub fn ws_cmt(& mut self) {
//     let mut chars = string[cursor..].chars() ;
//     let mut cnt = 0 ;
//     'ws_cmt: while let Some(char) = chars.next() {
//       cnt += 1 ;
//       if ! char.is_whitespace() {
//         if char == ';' {
//           'comment: while let Some( (_, char) ) = self.next() {
//             match char {
//               '\n' => break 'comment,
//               _ => (),
//             }
//           }
//         } else {
//           self.cursor += 
//           break 'ws_cmt
//         }
//       }
//     }
//   }
// }


