// See the LICENSE files at the top-level directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! SMT Lib 2 result parsers.

use errors::* ;

/// Parses a sequence of tags.
macro_rules! tags {
  ( $p:expr => $($e:expr),+ ) => (
    $(
      $p.tag($e) ? ;
    )+
  ) ;
}

use std::io::BufRead ;

/// SMT-LIB 2.0 parser.
pub struct SmtParser<R: BufRead> {
  /// Reader being parsed.
  input: R,
  /// Buffer we are reading to.
  buff: String,
  /// Second buffer for swapping.
  buff_2: String,
  /// Current position in the text.
  cursor: usize,
  /// Marked position, for backtracking.
  mark: Option<usize>,
}
impl<R: BufRead> SmtParser<R> {
  /// Creates an smt parser.
  pub fn new(input: R) -> Self {
    SmtParser {
      input,
      buff: String::with_capacity(10_000),
      buff_2: String::with_capacity(10_000),
      cursor: 0,
      mark: None,
    }
  }

  /// Reads a line from the input.
  pub fn read_line(& mut self) -> Res<()> {
    self.input.read_line(& mut self.buff) ? ;
    Ok(())
  }

  pub fn get_sexpr_byte(& mut self) -> Res<& [u8]> {
    Ok( self.get_sexpr()?.as_bytes() )
  }

  pub fn get_sexpr(& mut self) -> Res<& str> {
    let end = self.load_sexpr() ? ;
    let start = self.cursor ;
    self.cursor = end ;
    Ok( & self.buff[ start .. end ] )
  }

  /// Loads lines until a full s-expr is loaded.
  ///
  /// Returns the next position of the end of the sexpr. The cursor will be
  /// set at its beginning.
  pub fn load_sexpr(& mut self) -> Res<usize> {
    self.spc_cmt() ;
    // self.print("") ;
    let (mut op_paren, mut cl_paren) = (0, 0) ;
    let mut quoted_ident = false ;
    let mut start = self.cursor ;
    let mut end = start ;

    // println!("  loading:") ;
    'load: loop {
      if start == self.buff.len() {
        self.read_line() ?
      }
      debug_assert!(op_paren >= cl_paren) ;

      'lines: for line in self.buff[start..].lines() {
        debug_assert!(op_paren >= cl_paren) ;
        // println!("  > {}", line) ;
        let mut this_end = start ;
        let mut chars = line.chars() ;
        'this_line: while let Some(c) = chars.next() {
          debug_assert!(op_paren >= cl_paren) ;
          this_end += 1 ;
          // println!("  '{}' {}/{} |{}|", c, op_paren, cl_paren, quoted_ident) ;
          
          if quoted_ident {
            quoted_ident = c != '|' ;
            if ! quoted_ident && op_paren == 0 {
              end = this_end ;
              break 'load
            }
          } else {
            match c {
              ';' => break 'this_line,
              '|' => quoted_ident = ! quoted_ident,
              '(' => op_paren += 1,
              ')' => {
                cl_paren += 1 ;
                if op_paren == cl_paren {
                  end = this_end ;
                  break 'load
                }
              },
              _ => if ! c.is_whitespace() && op_paren == 0 {
                // print!("... `") ;
                'token: for c in chars {
                  if c.is_whitespace() { break 'token }
                  match c {
                    ')' | '(' | '|' => {
                      // println!("` | {}", this_end) ;
                      break 'token
                    },
                    _ => {
                      // print!("{}[{}]", c, this_end) ;
                      this_end += 1
                    },
                  }
                }
                end = this_end ;
                break 'load
              },
            }
          }

        }

      }
      if start == self.buff.len() { break 'load }
      start = self.buff.len()

    }
    self.spc_cmt() ;
    // println!("{} .. {}", self.cursor, end) ;
    Ok(end)
  }

  /// Clears the buffer up to the cursor position.
  pub fn clear(& mut self) {
    debug_assert!( self.buff_2.is_empty() ) ;
    self.buff_2.push_str( & self.buff[self.cursor..] ) ;
    self.buff.clear() ;
    ::std::mem::swap(& mut self.buff, & mut self.buff_2) ;
    self.cursor = 0 ;
  }

  /// Prints itself.
  pub fn print(& self, pref: & str) {
    let mut count = 0 ;
    let mut printed_cursor = false ;
    for line in self.buff.lines() {
      println!("{}|`{}`", pref, line) ;
      if ! printed_cursor {
        let nu_count = count + line.len() + 1 ;
        if self.cursor <= nu_count {
          printed_cursor = true ;
          println!(
            "{0}| {1: >2$}^",
            pref, "", self.cursor - count
          )
        }
        count = nu_count ;
      }
    }
  }

  /// Parses some spaces or some comments.
  pub fn spc_cmt(& mut self) {
    let mut chars = self.buff[self.cursor..].chars() ;
    'spc_cmt: while let Some(c) = chars.next() {
      if ! c.is_whitespace() {
        if c == ';' {
          self.cursor += 1 ;
          'skip_line: while let Some(c) = chars.next() {
            self.cursor += 1 ;
            if c == '\n' || c == '\r' {
              break 'skip_line
            }
          }
        } else {
          break 'spc_cmt
        }
      } else {
        self.cursor += 1 ;
      }
    }
  }

  /// Tries to parse a tag, `true` if successful.
  pub fn try_tag(& mut self, tag: & str) -> Res<bool> {
    loop {
      self.spc_cmt() ;
      if self.cursor + tag.len() >= self.buff.len() + 1 {
        self.read_line() ?
      } else {
        if & self.buff[ self.cursor .. self.cursor + tag.len() ] == tag {
          self.cursor += tag.len() ;
          return Ok(true)
        } else {
          return Ok(false)
        }
      }
    }
  }
  /// Parses a tag or fails.
  pub fn tag(& mut self, tag: & str) -> Res<()> {
    if self.try_tag(tag) ? {
      Ok(())
    } else {
      self.fail_with( format!("expected `{}`", tag) )
    }
  }

  /// Marks the current position.
  pub fn mark(& mut self) {
    debug_assert!( self.mark.is_none() ) ;
    self.mark = Some(self.cursor)
  }
  /// Clears the marked position.
  pub fn clear_mark(& mut self) {
    debug_assert!( self.mark.is_some() ) ;
    self.mark = None
  }
  /// Backtracks to the marked position.
  pub fn backtrack(& mut self) {
    if let Some(position) = self.mark {
      self.cursor = position ;
      self.mark = None
    } else {
      panic!("cannot backtrack, no marked position")
    }
  }

  /// Tries to parse a sequence of things potentially separated by whitespaces
  /// and/or comments.
  pub fn try_seq<
    'a, Tags: IntoIterator<Item = & 'a str>
  >(& mut self, tags: Tags) -> Res<bool> {
    self.mark() ;
    for tag in tags {
      if ! self.try_tag(tag) ? {
        self.backtrack() ;
        return Ok(false)
      }
    }
    Ok(true)
  }

  /// Parses a sequence of things potentially separated by whitespaces and/or
  /// comments.
  pub fn seq<
    'a, Tags: IntoIterator<Item = & 'a str>
  >(& mut self, tags: Tags) -> Res<()> {
    for tag in tags { self.tag(tag) ? }
    Ok(())
  }


  /// Generates a failure.
  pub fn fail_with<T, Str: Into<String>>(& mut self, msg: Str) -> Res<T> {
    let sexpr = self.get_sexpr().chain_err(
      || "while retrieving sexpression for parse error"
    )?.to_string() ;
    if sexpr == "unsupported" {
      bail!(ErrorKind::Unsupported)
    } else {
      bail!(
        ErrorKind::ParseError(msg.into(), sexpr)
      )
    }
  }

  /// Parses `success`.
  pub fn success(& mut self) -> Res<()> {
    self.tag("success")
  }



  /// Parses the result of a check-sat.
  pub fn check_sat(& mut self) -> Res< Option<bool> > {
    if self.try_tag("sat") ? {
      Ok(Some(true))
    } else if self.try_tag("unsat") ? {
      Ok(Some(false))
    } else if self.try_tag("unknown") ? {
      Ok(None)
    } else {
      self.fail_with("expected `sat` or `unsat`")
    }
  }


  /// Parses the result of a get-model where all symbols are nullary.
  pub fn get_model_const<Ident, Value, Type, Parser>(
    & mut self, parser: Parser
  ) -> Res< Vec<(Ident, Type, Value)> >
  where Parser: IdentParser<Ident, Type> + ValueParser<Value> {
    let mut model = Vec::new() ;
    tags!{ self => "(", "model" }
    while ! self.try_tag(")") ? {
      tags!{ self => "(", "define-fun" }
      let id = parser.parse_ident( self.get_sexpr() ? ) ? ;
      tags!{ self => "(", ")" }
      let typ = parser.parse_type( self.get_sexpr() ? ) ? ;
      let value = parser.parse_value( self.get_sexpr() ? ) ? ;
      model.push( (id, typ, value) ) ;
      tags!{ self => ")" }
    }
    Ok(model)
  }


  /// Parses the result of a get-model.
  pub fn get_model<Ident, Value, Type, Parser>(
    & mut self, parser: Parser
  ) -> Res< Vec<(Ident, Vec<Type>, Type, Value)> >
  where Parser: IdentParser<Ident, Type> + ValueParser<Value> {
    let mut model = Vec::new() ;
    tags!{ self => "(", "model" }
    while ! self.try_tag(")") ? {
      tags!{ self => "(", "define-fun" }
      let id = parser.parse_ident( self.get_sexpr() ? ) ? ;
      tags!{ self => "(" }
      let mut args = Vec::new() ;
      while ! self.try_tag(")") ? {
        let typ = parser.parse_type(self.get_sexpr() ? ) ? ;
        args.push(typ)
      }
      let typ = parser.parse_type( self.get_sexpr() ? ) ? ;
      let value = parser.parse_value( self.get_sexpr() ? ) ? ;
      model.push( (id, args, typ, value) ) ;
      tags!{ self => ")" }
    }
    Ok(model)
  }

  /// Parses the result of a get-value.
  pub fn get_values<Value, Info: Clone, Expr, Parser>(
    & mut self, parser: Parser, info: Info
  ) -> Res< Vec<(Expr, Value)> >
  where Parser: ValueParser<Value> + ExprParser<Expr, Info> {
    let mut values = Vec::new() ;
    tags!{ self => "(" }
    while ! self.try_tag(")") ? {
      tags!{ self => "(" }
      let expr = parser.parse_expr( self.get_sexpr() ?, info.clone() ) ? ;
      let value = parser.parse_value( self.get_sexpr() ? ) ? ;
      values.push( (expr, value) ) ;
      tags!{ self => ")" }
    }
    Ok(values)
  }

}




/// Can parse an ident.
pub trait IdentParser<Ident, Type, Input = str>: Copy
where Input: ?Sized {
  fn parse_ident(self, & Input) -> Res<Ident> ;
  fn parse_type(self, & Input) -> Res<Type> ;
}
impl<Ident, Type, T> IdentParser<Ident, Type> for T
where T: IdentParser<Ident, Type, [u8]> {
  fn parse_ident(self, input: & str) -> Res<Ident> {
    self.parse_ident( input.as_bytes() )
  }
  fn parse_type(self, input: & str) -> Res<Type> {
    self.parse_type( input.as_bytes() )
  }
}

/// Can parse a value.
pub trait ValueParser<Value, Input = str>: Copy
where Input: ?Sized {
  fn parse_value(self, & Input) -> Res<Value> ;
}
impl<Value, T> ValueParser<Value> for T
where T: ValueParser<Value, [u8]> {
  fn parse_value(self, input: & str) -> Res<Value> {
    self.parse_value( input.as_bytes() )
  }
}

/// Can parse an expression.
pub trait ExprParser<Expr, Info, Input = str>: Copy
where Input: ?Sized {
  fn parse_expr(self, & Input, Info) -> Res<Expr> ;
}
impl<Expr, Info, T> ExprParser<Expr, Info> for T
where T: ExprParser<Expr, Info, [u8]> {
  fn parse_expr(self, input: & str, info: Info) -> Res<Expr> {
    self.parse_expr( input.as_bytes(), info )
  }
}

/// Can parse a proof.
pub trait ProofParser<Proof, Input = str>: Copy
where Input: ?Sized {
  fn parse_proof(self, & Input) -> Res<Proof> ;
}
impl<Proof, T> ProofParser<Proof> for T
where T: ProofParser<Proof, [u8]> {
  fn parse_proof(self, input: & str) -> Res<Proof> {
    self.parse_proof( input.as_bytes() )
  }
}
