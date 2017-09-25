//! SMT Lib 2 result parsers.
//!
//! Depending on the commands you plan to use, your parser will need to
//! implement
//!
//! |                                         | for                         |
//! |:---------------------------------------:|:---------------------------:|
//! | [`IdentParser`](trait.IdentParser.html) | `get-model`                 |
//! | [`ValueParser`](trait.ValueParser.html) | `get-model` and `get-value` |
//! | [`ExprParser`](trait.ExprParser.html)   | `get-value`                 |
//! | [`ProofParser`](trait.ExprParser.html)  | *currently unused*          |
//!
//! You can choose the kind of input you want to parse, between
//!
//! - `& [u8]`, *e.g.* for [`nom`][nom],
//! - `& str`, *e.g.* for [`regex`][regex],
//! - [`& mut SmtParser`][parser], `rmst2`'s internal parser which
//!   provides simple helpers to parse s-expressions.
//!
//! The first two are safe in that your parsers will be called on the tokens
//! they are supposed to parse and nothing else.
//!
//! ```
//! # extern crate rsmt2 ;
//! # use rsmt2::parse::SmtParser ;
//! # fn main() {
//! use rsmt2::parse::{ IdentParser, ValueParser } ;
//! use rsmt2::SmtRes ;
//! let txt = "\
//!   ( model (define-fun a () Int (- 17)) )
//! " ;
//! let mut parser = SmtParser::of_str(txt) ;
//!
//! struct Parser ;
//! impl<'a, 'b> ValueParser<'a, String, & 'a str> for & 'b Parser {
//!   fn parse_value(self, input: & 'a str) -> SmtRes<String> {
//!     Ok(input.into())
//!   }
//! }
//! impl<'a, 'b> IdentParser<'a, String, String, & 'a str> for & 'b Parser {
//!   fn parse_ident(self, input: & 'a str) -> SmtRes<String> {
//!     Ok(input.into())
//!   }
//!   fn parse_type(self, input: & 'a str) -> SmtRes<String> {
//!     Ok(input.into())
//!   }
//! }
//!
//! let model = parser.get_model_const( & Parser ).expect("model") ;
//! assert_eq!( model, vec![ ("a".into(), "Int".into(), "(- 17)".into()) ] )
//! # }
//! ```
//!
//! But a parser taking `SmtParser` as input is "unsafe" in the sense that it
//! has access to the whole input. Note that `SmtParser` provides helper
//! parsing functions such as [`try_int`][try int] and [`try_sym`][try sym].
//!
//! ```
//! # extern crate rsmt2 ;
//! # use rsmt2::parse::SmtParser ;
//! # fn main() {
//! use rsmt2::parse::{ IdentParser, ValueParser } ;
//! use rsmt2::errors::SmtRes ;
//! let txt = "\
//!   ( model (define-fun a () Int (- 17)) )
//! " ;
//! let mut parser = SmtParser::of_str(txt) ;
//!
//! struct Parser ;
//! impl<'a, 'b, Br: ::std::io::BufRead> ValueParser<
//!   'a, String, & 'a mut SmtParser<Br>
//! > for & 'b Parser {
//!   fn parse_value(self, input: & 'a mut SmtParser<Br>) -> SmtRes<String> {
//!     input.tag("(- 17))") ? ; Ok( "-17".into() )
//!     //               ^~~~~ eating more input than we should...
//!   }
//! }
//! impl<'a, 'b, Br: ::std::io::BufRead> IdentParser<
//!   'a, String, String, & 'a mut SmtParser<Br>
//! > for & 'b Parser {
//!   fn parse_ident(self, input: & 'a mut SmtParser<Br>) -> SmtRes<String> {
//!     input.tag("a") ? ; Ok( "a".into() )
//!   }
//!   fn parse_type(self, input: & 'a mut SmtParser<Br>) -> SmtRes<String> {
//!     input.tag("Int") ? ; Ok( "Int".into() )
//!   }
//! }
//!
//! use rsmt2::errors::ErrorKind ;
//! match * parser.get_model_const( & Parser ).unwrap_err().kind() {
//!   ErrorKind::ParseError(ref msg, ref token) => {
//!     assert_eq!(
//!       msg, "expected `(` opening define-fun or `)` closing model"
//!     ) ;
//!     assert_eq!(token, "eof")
//!   },
//!   ref error => panic!("unexpected error: {}", error)
//! }
//! # }
//! ```
//!
//! [nom]: https://crates.io/crates/nom (nom crate on crates.io)
//! [regex]: https://crates.io/crates/regex (regex crate on crates.io)
//! [parser]: struct.SmtParser.html (rsmt2's internal parser)
//! [try int]: struct.SmtParser.html#method.try_int (try_int function)
//! [try sym]: struct.SmtParser.html#method.try_sym (try_sym function)

use errors::* ;

use std::io::{ BufRead, BufReader } ;



/// Tries a user parser.
macro_rules! try_apply {
  ($e:expr => |$res:pat| $do:expr, $msg:expr) => (
    match $e {
      Ok($res) => $do,
      Err(e) => bail!("{}: {}", $msg, e)
    }
  ) ;
}


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
impl<'a> SmtParser< BufReader<& 'a [u8]> > {
  /// Constructor from a string, mostly for doc/test purposes.
  pub fn of_str(s: & 'a str) -> Self {
    SmtParser::new( BufReader::new( s.as_bytes() ) )
  }
}
impl<R: BufRead> SmtParser<R> {
  /// Creates an smt parser.
  pub fn new(input: R) -> Self {
    SmtParser {
      input,
      buff: String::with_capacity(5_000),
      buff_2: String::with_capacity(5_000),
      cursor: 0,
      mark: None,
    }
  }

  /// Immutable access to the buffer.
  pub fn buff(& self) -> & str {
    & self.buff
  }
  /// Immutable access to the part of the buffer that's not been parsed yet.
  pub fn buff_rest(& self) -> & str {
    & self.buff[ self.cursor .. ]
  }
  /// The current position in the buffer.
  pub fn cursor(& self) -> usize {
    self.cursor
  }

  /// Reads a line from the input. Returns `true` if something was read.
  fn read_line(& mut self) -> SmtRes<bool> {
    let read = self.input.read_line(& mut self.buff) ? ;
    Ok( read != 0 )
  }

  /// Returns the next s-expression and positions the cursor directly after it.
  ///
  /// An s-expression is an ident, a constant with no parens (`42`, `false`,
  /// *etc.*), or something between (nested) parens. 
  ///
  /// ```
  /// # extern crate rsmt2 ;
  /// # use rsmt2::parse::SmtParser ;
  /// # fn main() {
  /// let txt = "\
  ///   token  ; a comment\n\n next_token ; more comments\n\
  ///   (+ |quoted ident, ; a comment\n parens don't count)| 7)42 false\
  /// " ;
  /// let mut parser = SmtParser::of_str(txt) ;
  ///
  /// assert_eq!( parser.get_sexpr().unwrap(), "token" ) ;
  /// assert_eq!( parser.buff_rest(), "  ; a comment\n" ) ;
  ///
  /// assert_eq!( parser.get_sexpr().unwrap(), "next_token" ) ;
  /// assert_eq!( parser.buff_rest(), " ; more comments\n" ) ;
  ///
  /// assert_eq!(
  ///   parser.get_sexpr().unwrap(),
  ///   "(+ |quoted ident, ; a comment\n parens don't count)| 7)"
  /// ) ;
  /// assert_eq!( parser.buff_rest(), "42 false" ) ;
  ///
  /// assert_eq!( parser.get_sexpr().unwrap(), "42" ) ;
  /// assert_eq!( parser.buff_rest(), " false" ) ;
  ///
  /// assert_eq!( parser.get_sexpr().unwrap(), "false" ) ;
  /// assert_eq!( parser.buff_rest(), "" ) ;
  /// # }
  /// ```
  pub fn get_sexpr(& mut self) -> SmtRes<& str> {
    let end = self.load_sexpr() ? ;
    let start = self.cursor ;
    self.cursor = end ;
    Ok( & self.buff[ start .. end ] )
  }

  /// Loads lines until a full s-expr is loaded.
  ///
  /// Returns the next position of the end of the sexpr. The cursor will be
  /// set at its beginning.
  fn load_sexpr(& mut self) -> SmtRes<usize> {
    self.spc_cmt() ;
    // self.print("") ;
    let (mut op_paren, mut cl_paren) = (0, 0) ;
    let mut quoted_ident = false ;
    let mut start = self.cursor ;
    let mut end = start ;

    // println!("  loading:") ;
    'load: loop {
      if start == self.buff.len() {
        let eof = ! self.read_line() ? ;
        if eof { bail!("reached eof") }
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
                    ')' | '(' | '|' | ';' => {
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

  /// Clears the buffer up to the current position.
  pub fn clear(& mut self) {
    self.spc_cmt() ;
    if ! self.cursor >= self.buff.len() {
      debug_assert!( self.buff_2.is_empty() ) ;
      self.buff_2.push_str( & self.buff[self.cursor..] ) ;
      self.buff.clear() ;
      ::std::mem::swap(& mut self.buff, & mut self.buff_2) ;
      self.cursor = 0
    } else {
      self.buff.clear() ;
      self.cursor = 0
    }
  }

  /// Prints itself, for debugging.
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
  ///
  /// Parsing a tag or loading an s-expression fetches new lines, this does
  /// not.
  ///
  /// ```
  /// # extern crate rsmt2 ;
  /// # use rsmt2::parse::SmtParser ;
  /// # fn main() {
  /// let txt = "  token  ; a comment\n\n next token ; last comment" ;
  /// let mut parser = SmtParser::of_str(txt) ;
  ///
  /// parser.spc_cmt() ;
  /// assert_eq!( parser.buff_rest(), "" ) ;
  /// assert_eq!( parser.buff(), "" ) ;
  ///
  /// assert!( parser.try_tag("token").expect("token") ) ;
  /// assert_eq!( parser.buff_rest(), "  ; a comment\n" ) ;
  /// assert_eq!( parser.buff(), "  token  ; a comment\n" ) ;
  ///
  /// parser.spc_cmt() ;
  /// assert_eq!( parser.buff_rest(), "" ) ;
  /// assert_eq!( parser.buff(), "  token  ; a comment\n" ) ;
  ///
  /// assert!( parser.try_tag("next token").expect("token") ) ;
  /// assert_eq!( parser.buff_rest(), " ; last comment" ) ;
  /// assert_eq!( parser.buff(), txt ) ;
  ///
  /// parser.spc_cmt() ;
  /// assert_eq!( parser.buff_rest(), "" ) ;
  /// assert_eq!( parser.buff(), txt ) ;
  /// # }
  /// ```
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

  /// Tries to parse a tag, `true` if successful. Parse whitespaces and
  /// comments if any before the token.
  ///
  /// If this function returns `false`, then the cursor is at the first
  /// non-whitespace non-commented character after the original cursor
  /// position.
  ///
  /// ```
  /// # extern crate rsmt2 ;
  /// # use rsmt2::parse::SmtParser ;
  /// # fn main() {
  /// let txt = "\
  ///   a tag is anything  |(>_<)|  ; a comment\n\n next token ; last comment\
  /// " ;
  /// let mut parser = SmtParser::of_str(txt) ;
  /// assert!( parser.try_tag("a tag is anything").expect("tag") ) ;
  /// assert_eq!( parser.buff_rest(), "  |(>_<)|  ; a comment\n" ) ;
  /// assert!( ! parser.try_tag("not the token").expect("tag") ) ;
  /// assert_eq!( parser.buff_rest(), "|(>_<)|  ; a comment\n" ) ;
  /// assert!( parser.try_tag("|(>_<)|").expect("tag") ) ;
  /// assert!( ! parser.try_tag("not the next token").expect("tag") ) ;
  /// assert_eq!( parser.buff_rest(), "next token ; last comment" ) ;
  /// assert!( parser.try_tag("next token").expect("tag") ) ;
  /// # }
  /// ```
  pub fn try_tag(& mut self, tag: & str) -> SmtRes<bool> {
    loop {
      self.spc_cmt() ;
      if self.cursor + tag.len() >= self.buff.len() + 1 {
        // println!("reading ({})", tag) ;
        let eof = ! self.read_line() ? ;
        self.spc_cmt() ;
        if eof { return Ok(false) }
      } else {
        if & self.buff[ self.cursor .. self.cursor + tag.len() ] == tag {
          self.cursor += tag.len() ;
          return Ok(true)
        } else {
          self.spc_cmt() ;
          return Ok(false)
        }
      }
    }
  }
  /// Parses a tag or fails.
  ///
  /// Returns `()` exactly when [`try_tag`][try tag] returns `true`, and an
  /// error otherwise.
  ///
  /// [try tag]: struct.SmtParser.html#method.try_tag (try_tag function)
  pub fn tag(& mut self, tag: & str) -> SmtRes<()> {
    if self.try_tag(tag) ? {
      Ok(())
    } else {
      self.fail_with( format!("expected `{}`", tag) )
    }
  }
  /// Parses a tag or fails, appends `err_msg` at the end of the error message.
  ///
  /// Returns `()` exactly when [`try_tag`][try tag] returns `true`, and an
  /// error otherwise.
  ///
  /// [try tag]: struct.SmtParser.html#method.try_tag (try_tag function)
  pub fn tag_info(& mut self, tag: & str, err_msg: & str) -> SmtRes<()> {
    if self.try_tag(tag) ? {
      Ok(())
    } else {
      self.fail_with( format!("expected `{}` {}", tag, err_msg) )
    }
  }

  /// Parses a tag followed by a whitespace, a paren or a comment.
  ///
  /// If this function returns `false`, then the cursor is at the first
  /// non-whitespace non-commented character after the original cursor
  /// position.
  ///
  /// ```
  /// # extern crate rsmt2 ;
  /// # use rsmt2::parse::SmtParser ;
  /// # fn main() {
  /// let txt = "\
  ///   a word is anything  |(>_<)|  last; comment\
  /// " ;
  /// let mut parser = SmtParser::of_str(txt) ;
  /// assert!( parser.try_word("a word is").expect("word") ) ;
  /// assert_eq!( parser.buff_rest(), " anything  |(>_<)|  last; comment" ) ;
  /// assert!( ! parser.try_word("a").expect("word") ) ;
  /// assert_eq!( parser.buff_rest(), "anything  |(>_<)|  last; comment" ) ;
  /// assert!( ! parser.try_word("any").expect("word") ) ;
  /// assert_eq!( parser.buff_rest(), "anything  |(>_<)|  last; comment" ) ;
  /// assert!( ! parser.try_word("anythin").expect("word") ) ;
  /// assert_eq!( parser.buff_rest(), "anything  |(>_<)|  last; comment" ) ;
  /// assert!( parser.try_word("anything").expect("word") ) ;
  /// assert_eq!( parser.buff_rest(), "  |(>_<)|  last; comment" ) ;
  /// assert!( parser.try_word("|").expect("word") ) ;
  /// assert_eq!( parser.buff_rest(), "(>_<)|  last; comment" ) ;
  /// assert!( parser.try_tag("(").expect("tag") ) ;
  /// assert_eq!( parser.buff_rest(), ">_<)|  last; comment" ) ;
  /// assert!( parser.try_word(">_<").expect("word") ) ;
  /// assert_eq!( parser.buff_rest(), ")|  last; comment" ) ;
  /// assert!( parser.try_tag(")").expect("tag") ) ;
  /// assert_eq!( parser.buff_rest(), "|  last; comment" ) ;
  /// assert!( parser.try_word("|").expect("word") ) ;
  /// assert_eq!( parser.buff_rest(), "  last; comment" ) ;
  /// assert!( parser.try_word("last").expect("word") ) ;
  /// assert_eq!( parser.buff_rest(), "; comment" ) ;
  /// # }
  /// ```
  pub fn try_word(& mut self, word: & str) -> SmtRes<bool> {
    self.mark() ;
    if self.try_tag(word) ? {
      if let Some(c) = self.buff[ self.cursor .. ].chars().next() {
        if c.is_whitespace() || c == ')' || c == '(' || c == ';' {
          self.clear_mark() ;
          return Ok(true)
        }
      }
    }
    self.backtrack() ;
    self.spc_cmt() ;
    Ok(false)
  }

  /// Marks the current position.
  #[inline]
  fn mark(& mut self) {
    debug_assert!( self.mark.is_none() ) ;
    self.mark = Some(self.cursor)
  }
  /// Clears the marked position.
  #[inline]
  fn clear_mark(& mut self) {
    debug_assert!( self.mark.is_some() ) ;
    self.mark = None
  }
  /// Backtracks to the marked position.
  fn backtrack(& mut self) {
    if let Some(position) = self.mark {
      self.cursor = position ;
      self.clear_mark() ;
    } else {
      panic!("cannot backtrack, no marked position")
    }
  }

  /// Tries to parse a sequence of things potentially separated by whitespaces
  /// and/or comments.
  ///
  /// If this function returns `false`, then the cursor is at the first
  /// non-whitespace non-commented character after the original cursor
  /// position.
  ///
  /// ```
  /// # extern crate rsmt2 ;
  /// # use rsmt2::parse::SmtParser ;
  /// # fn main() {
  /// let txt = "\
  ///   a tag is anything  |(>_<)|  ; a comment\n\n next token ; last comment\
  /// " ;
  /// let mut parser = SmtParser::of_str(txt) ;
  /// assert!(
  ///   parser.try_tags(
  ///      &[ "a", "tag", "is anything", "|", "(", ">_<", ")", "|" ]
  ///   ).expect("tags")
  /// ) ;
  /// assert_eq!( parser.buff_rest(), "  ; a comment\n" ) ;
  /// assert!(
  ///   ! parser.try_tags(
  ///     & [ "next", "token", "something else?" ]
  ///   ).expect("tags")
  /// ) ;
  /// assert_eq!( parser.buff_rest(), "next token ; last comment" )
  /// # }
  /// ```
  pub fn try_tags<'a, Tags, S>(& mut self, tags: & 'a Tags) -> SmtRes<bool>
  where & 'a Tags: IntoIterator<Item = S>, S: AsRef<str> {
    self.mark() ;
    for tag in tags {
      if ! self.try_tag( tag.as_ref() ) ? {
        self.backtrack() ;
        self.spc_cmt() ;
        return Ok(false)
      }
    }
    self.clear_mark() ;
    Ok(true)
  }

  /// Parses a sequence of things potentially separated by whitespaces and/or
  /// comments.
  ///
  /// Returns `()` exactly when [`try_tags`][try tags] returns `true`, and an
  /// error otherwise.
  ///
  /// [try tags]: struct.SmtParser.html#method.try_tag (try_tag function)
  pub fn tags<'a, Tags, S>(& mut self, tags: & 'a Tags) -> SmtRes<()>
  where & 'a Tags: IntoIterator<Item = S>, S: AsRef<str> {
    for tag in tags { self.tag( tag.as_ref() ) ? }
    Ok(())
  }


  /// Generates a failure at the current position.
  pub fn fail_with<T, Str: Into<String>>(& mut self, msg: Str) -> SmtRes<T> {
    self.print("") ;
    let sexpr = match self.get_sexpr() {
      Ok(e) => Some( e.to_string() ),
      _ => None,
    } ;
    let sexpr = if let Some(e) = sexpr { e } else {
      if self.cursor < self.buff.len() {
        let mut stuff = self.buff[ self.cursor .. ].trim().split_whitespace() ;
        if let Some(stuff) = stuff.next() {
          stuff.to_string()
        } else {
          " ".to_string()
        }
      } else {
        "eof".to_string()
      }
    } ;
    if sexpr == "unsupported" {
      bail!(ErrorKind::Unsupported)
    } else {
      bail!(
        ErrorKind::ParseError(msg.into(), sexpr)
      )
    }
  }

  /// Tries to parse a boolean.
  ///
  /// ```
  /// # extern crate rsmt2 ;
  /// # use rsmt2::parse::SmtParser ;
  /// # fn main() {
  /// let txt = "\
  ///   true fls  true_ly_bad_ident false; comment\
  /// " ;
  /// let mut parser = SmtParser::of_str(txt) ;
  /// assert_eq!( parser.try_bool().expect("bool"), Some(true) ) ;
  /// assert_eq!(
  ///   parser.buff_rest(), " fls  true_ly_bad_ident false; comment"
  /// ) ;
  /// assert_eq!( parser.try_bool().expect("bool"), None ) ;
  /// assert_eq!(
  ///   parser.buff_rest(), "fls  true_ly_bad_ident false; comment"
  /// ) ;
  /// parser.tag("fls").expect("tag") ;
  /// assert_eq!( parser.try_bool().expect("bool"), None ) ;
  /// assert_eq!(
  ///   parser.buff_rest(), "true_ly_bad_ident false; comment"
  /// ) ;
  /// parser.tag("true_ly_bad_ident").expect("tag") ;
  /// assert_eq!( parser.try_bool().expect("bool"), Some(false) ) ;
  /// assert_eq!(
  ///   parser.buff_rest(), "; comment"
  /// ) ;
  /// # }
  /// ```
  pub fn try_bool(& mut self) -> SmtRes< Option<bool> > {
    if self.try_word("true") ? {
      Ok( Some(true) )
    } else if self.try_word("false") ? {
      Ok( Some(false) )
    } else {
      Ok( None )
    }
  }

  /// Tries to parse an unsigned integer. Does **not** load, backtrack, or
  /// mark. Returns start and end positions.
  #[inline]
  fn try_uint_indices(& self) -> SmtRes< Option<(usize, usize)> > {
    let mut end = self.cursor ;
    for c in self.buff[ self.cursor .. ].chars() {
      if c.is_numeric() {
        end += 1
      } else {
        break
      }
    }
    if end > self.cursor {
      Ok( Some( (self.cursor, end) ) )
    } else { Ok(None) }
  }

  /// Tries to parse an unsigned integer. Does **not** load, backtrack, or
  /// mark, but moves the cursor to the end of the integer if any.
  #[inline]
  fn try_uint(& mut self) -> SmtRes< Option<& str> > {
    self.spc_cmt() ;
    if let Some((start, end)) = self.try_uint_indices() ? {
      self.cursor = end ;
      Ok( Some( & self.buff[ start .. end ] ) )
    } else {
      Ok(None)
    }
  }

  /// Tries to parses an integer.
  ///
  /// Parameters of the input function:
  ///
  /// - the absolute value of the integer parsed,
  /// - positiveness flag: `true` iff the integer is positive.
  ///
  /// **NB**: input function `f` cannot return the input string in any way.
  /// Doing so will not borrow-check and is completely unsafe as the parser can
  /// and in general will discard what's in its buffer once it's parsed.
  ///
  /// Only recognizes integers of the form
  ///
  /// ```bash
  /// int   ::= usize
  ///         | '(' '-' usize ')'
  /// usize ::= [0-9][0-9]*
  /// ```
  ///
  /// ```
  /// # extern crate rsmt2 ;
  /// # use rsmt2::parse::SmtParser ;
  /// # fn main() {
  /// use std::str::FromStr ;
  /// fn to_int(
  ///   input: & str, positive: bool
  /// ) -> Result<isize, <isize as FromStr>::Err> {
  ///   isize::from_str(input).map(
  ///     |num| if positive { num } else { - num }
  ///   )
  /// }
  /// let txt = "\
  ///   666 (- 11) false; comment\n(+ 31) (= tru)\
  /// " ;
  /// let mut parser = SmtParser::of_str(txt) ;
  /// assert_eq!( parser.try_int(to_int).expect("int"), Some(666) ) ;
  /// assert_eq!(
  ///   parser.buff_rest(), " (- 11) false; comment\n"
  /// ) ;
  /// assert_eq!( parser.try_int(to_int).expect("int"), Some(- 11) ) ;
  /// assert_eq!(
  ///   parser.buff_rest(), " false; comment\n"
  /// ) ;
  /// assert_eq!( parser.try_int(to_int).expect("int"), None ) ;
  /// parser.tag("false").expect("tag") ;
  /// assert_eq!( parser.try_int(to_int).expect("int"), Some(31) ) ;
  /// assert_eq!(
  ///   parser.buff_rest(), " (= tru)"
  /// ) ;
  /// assert_eq!( parser.try_int(to_int).expect("int"), None ) ;
  /// # }
  /// ```
  pub fn try_int<F, T, Err>(& mut self, f: F) -> SmtRes< Option<T> >
  where F: FnOnce(& str, bool) -> Result<T, Err>, Err: ::std::fmt::Display {
    self.load_sexpr() ? ;
    self.mark() ;
    let mut res = None ;
    if let Some((start, end)) = self.try_uint_indices() ? {
      self.cursor = end ;
      let uint = & self.buff[start .. end] ;
      try_apply!(
        f(uint, true) => |int| res = Some(int),
        format!("error parsing integer `{}`", uint)
      )
    } else if self.try_tag("(") ? {
      let pos = if self.try_tag("-") ? {
        false
      } else if self.try_tag("+") ? {
        true
      } else {
        self.backtrack() ;
        return Ok(None)
      } ;
      if let Some(uint) = self.try_uint() ? {
        match f(uint, pos) {
          Ok(int) => res = Some(int),
          Err(e) => {
            let uint = if ! pos {
              format!("(- {})", uint)
            } else { uint.into() } ;
            bail!("error parsing integer `{}`: {}", uint, e)
          },
        }
      }
      if res.is_some() {
        self.tag(")") ?
      } else {
        self.backtrack() ;
        return Ok(None)
      }
    }
    if res.is_none() { self.backtrack() } else { self.clear_mark() }
    Ok(res)
  }


  /// Tries to parses a rational (called *Real* in SMT-LIB).
  ///
  /// Parameters of the input function:
  ///
  /// - numerator of the rational parsed (> 0),
  /// - denominator of the rational parsed (> 0),
  /// - positiveness flag: `true` iff the rational is positive.
  ///
  /// Only recognizes integers of the form
  ///
  /// ```bash
  /// rat   ::= '(' '/' udec udec ')'
  ///         | '(' '-' '(' '/' udec udec ')' ')'
  ///         | idec
  /// idec  ::= '(' '-' udec ')' | udec
  /// udec  ::= usize | usize.0
  /// usize ::= [0-9][0-9]*
  /// ```
  ///
  /// **NB**: input function `f` cannot return the input strings in any way.
  /// Doing so will not borrow-check and is completely unsafe as the parser can
  /// and in general will discard what's in its buffer once it's parsed.
  ///
  /// ```
  /// # extern crate rsmt2 ;
  /// # use rsmt2::parse::SmtParser ;
  /// # fn main() {
  /// use std::str::FromStr ;
  /// fn to_rat(
  ///   num: & str, den: & str, positive: bool
  /// ) -> Result<(isize, usize), String> {
  ///   let num = isize::from_str(num).map(
  ///     |num| if positive { num } else { - num }
  ///   ).map_err(|e| format!("{}", e)) ? ;
  ///   let den = usize::from_str(den).map_err(|e| format!("{}", e)) ? ;
  ///   Ok((num, den))
  /// }
  /// let txt = "\
  ///   666 (- 11) false; comment\n(/ 31 27) (- (/ 63 0)) (= tru)\
  /// " ;
  /// let mut parser = SmtParser::of_str(txt) ;
  /// assert_eq!( parser.try_rat(to_rat).expect("rat"), Some((666, 1)) ) ;
  /// assert_eq!(
  ///   parser.buff_rest(), " (- 11) false; comment\n"
  /// ) ;
  /// assert_eq!( parser.try_rat(to_rat).expect("rat"), Some((- 11, 1)) ) ;
  /// assert_eq!(
  ///   parser.buff_rest(), " false; comment\n"
  /// ) ;
  /// assert_eq!( parser.try_rat(to_rat).expect("rat"), None ) ;
  /// parser.tag("false").expect("tag") ;
  /// assert_eq!( parser.try_rat(to_rat).expect("rat"), Some((31, 27)) ) ;
  /// assert_eq!(
  ///   parser.buff_rest(), " (- (/ 63 0)) (= tru)"
  /// ) ;
  /// assert_eq!( parser.try_rat(to_rat).expect("rat"), (Some((- 63, 0))) ) ;
  /// # }
  /// ```
  pub fn try_rat<F, T, Err>(& mut self, f: F) -> SmtRes<Option<T>>
  where F: Fn(& str, & str, bool) -> Result<T, Err>, Err: ::std::fmt::Display {
    let err = "error parsing rational" ;
    self.load_sexpr() ? ;

    let mut res = None ;

    let pos = if self.try_tags( & [ "(", "-" ] ) ? {
      self.spc_cmt() ;
      false
    } else {
      true
    } ;

    if let Some((fst_start, fst_end)) = self.try_uint_indices() ? {
      if fst_end + 1 < self.buff.len()
      && & self.buff[ fst_end .. (fst_end + 2) ] == ".0" {
        self.cursor = fst_end + 2
      } else if fst_end < self.buff.len()
      && & self.buff[ fst_end .. (fst_end + 1) ] == "." {
        self.cursor = fst_end + 1
      } else {
        self.cursor = fst_end
      }
      try_apply!(
        f(
          & self.buff[fst_start..fst_end], "1", pos
        ) => |okay| res = Some(okay), err
      )
    }
    self.mark() ;

    if res.is_none() {

      if ! self.try_tag("(") ? {
        self.backtrack() ;
        return Ok(None)
      }

      if ! self.try_tag("/") ? {
        self.backtrack() ;
        return Ok(None)
      }

      self.spc_cmt() ;
      res = if let Some((num_start, num_end)) = self.try_uint_indices() ? {
        if num_end + 1 < self.buff.len()
        && & self.buff[ num_end .. (num_end + 2) ] == ".0" {
          self.cursor = num_end + 2
        } else if num_end < self.buff.len()
        && & self.buff[ num_end .. (num_end + 1) ] == "." {
          self.cursor = num_end + 1
        } else {
          self.cursor = num_end
        }
        self.spc_cmt() ;
        if let Some((den_start, den_end)) = self.try_uint_indices() ? {
          if den_end + 1 < self.buff.len()
          && & self.buff[ den_end .. (den_end + 2) ] == ".0" {
            self.cursor = den_end + 2
          } else if den_end < self.buff.len()
          && & self.buff[ den_end .. (den_end + 1) ] == "." {
            self.cursor = den_end + 1
          } else {
            self.cursor = den_end
          }
          match f(
            & self.buff[num_start .. num_end],
            & self.buff[den_start .. den_end],
            pos
          ) {
            Ok(res) => Some(res),
            Err(e) => bail!("error parsing rational: {}", e),
          }
        } else { None }
      } else { None } ;

      if res.is_some() {
        self.tag(")") ?
      }
    }

    if res.is_some() {
      if ! pos { self.tag(")") ? }
      self.clear_mark() ;
      Ok(res)
    } else {
      self.backtrack() ;
      Ok(None)
    }
  }

  /// Tries to parse a symbol.
  ///
  /// Quoted symbols (anything but `|` surrounded by `|`) are passed **with**
  /// the surrounding `|`.
  ///
  /// **NB**: input function `f` cannot return the input string in any way.
  /// Doing so will not borrow-check and is completely unsafe as the parser can
  /// and in general will discard what's in its buffer once it's parsed.
  ///
  /// ```
  /// # extern crate rsmt2 ;
  /// # use rsmt2::parse::SmtParser ;
  /// # fn main() {
  /// fn sym(input: & str) -> Result<String, String> {
  ///   Ok( input.into() )
  /// }
  /// let txt = "\
  ///   ident (- 11) +~stuff; comment\n |some stuff \n [{}!+)(}|\
  /// " ;
  /// let mut parser = SmtParser::of_str(txt) ;
  /// assert_eq!( parser.try_sym(sym).expect("sym"), Some("ident".into()) ) ;
  /// assert_eq!(
  ///   parser.buff_rest(), " (- 11) +~stuff; comment\n"
  /// ) ;
  /// assert_eq!( parser.try_sym(sym).expect("sym"), None ) ;
  /// assert_eq!(
  ///   parser.buff_rest(), "(- 11) +~stuff; comment\n"
  /// ) ;
  /// parser.tag("(- 11)").expect("tag") ;
  /// assert_eq!( parser.try_sym(sym).expect("sym"), Some("+~stuff".into()) ) ;
  /// assert_eq!(
  ///   parser.buff_rest(), "; comment\n"
  /// ) ;
  /// assert_eq!(
  ///   parser.try_sym(sym).expect("sym"),
  ///   Some("|some stuff \n [{}!+)(}|".into())
  /// ) ;
  /// # }
  /// ```
  pub fn try_sym<F, T, Err>(& mut self, f: F) -> SmtRes<Option<T>>
  where F: FnOnce(& str) -> Result<T, Err>, Err: ::std::fmt::Display {
    self.spc_cmt() ;
    let end = self.load_sexpr() ? ;
    let is_sym = if let Some(c) = self.buff[ self.cursor .. ].chars().next() {
      match c {
        _ if c.is_alphabetic() => true,
        '|' | '~' | '!' | '@' | '$' | '%' | '^' | '&' | '*' | '_' | '-' | '+' |
        '=' | '<' | '>' | '.' | '?' => true,
        _ => false,
      }
    } else {
      false
    } ;
    if is_sym {
      let ident = & self.buff[ self.cursor .. end ] ;
      self.cursor = end ;
      match f(ident) {
        Ok(res) => Ok( Some(res) ),
        Err(e) => bail!(
          "error parsing symbol `{}`: {}",
          & self.buff[ self.cursor .. end ], e
        ),
      }
    } else {
      Ok(None)
    }
  }

  /// Parses `success`.
  pub fn success(& mut self) -> SmtRes<()> {
    self.tag("success")
  }



  /// Parses the result of a check-sat.
  pub fn check_sat(& mut self) -> SmtRes< Option<bool> > {
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
  ) -> SmtRes< Vec<(Ident, Type, Value)> >
  where
  Parser: for<'a> IdentParser<'a, Ident, Type, & 'a mut Self> +
          for<'a> ValueParser<'a, Value, & 'a mut Self> {
    let mut model = Vec::new() ;
    self.tags( & ["(", "model"] ) ? ;
    while ! self.try_tag(")") ? {
      self.tag_info("(", "opening define-fun or `)` closing model") ? ;
      self.tag( "define-fun" ) ? ;
      let id = parser.parse_ident(self) ? ;
      self.tags( & ["(", ")"] ) ? ;
      let typ = parser.parse_type(self) ? ;
      let value = parser.parse_value(self) ? ;
      model.push( (id, typ, value) ) ;
      self.tag(")") ?
    }
    self.clear() ;
    Ok(model)
  }


  /// Parses the result of a get-model.
  pub fn get_model<Ident, Value, Type, Parser>(
    & mut self, parser: Parser
  ) -> SmtRes< Vec<(Ident, Vec<Type>, Type, Value)> >
  where
  Parser: for<'a> IdentParser<'a, Ident, Type, & 'a mut Self> +
          for<'a> ValueParser<'a, Value, & 'a mut Self> {
    let mut model = Vec::new() ;
    self.tags( &["(", "model"] ) ? ;
    while ! self.try_tag(")") ? {
      self.tag_info("(", "opening define-fun or `)` closing model") ? ;
      self.tag( "define-fun" ) ? ;
      let id = parser.parse_ident(self) ? ;
      self.tag("(") ? ;
      let mut args = Vec::new() ;
      while ! self.try_tag(")") ? {
        let typ = parser.parse_type(self) ? ;
        args.push(typ)
      }
      let typ = parser.parse_type(self) ? ;
      let value = parser.parse_value(self) ? ;
      model.push( (id, args, typ, value) ) ;
      self.tag(")") ? ;
    }
    self.clear() ;
    Ok(model)
  }

  /// Parses the result of a get-value.
  pub fn get_values<Value, Info: Clone, Expr, Parser>(
    & mut self, parser: Parser, info: Info
  ) -> SmtRes< Vec<(Expr, Value)> >
  where
  Parser: for<'a> ValueParser<'a, Value, & 'a mut Self> +
          for<'a> ExprParser<'a, Expr, Info, & 'a mut Self> {
    let mut values = Vec::new() ;
    self.tag("(") ? ;
    while ! self.try_tag(")") ? {
      self.tag_info(
        "(", "opening expr/value pair or `)` closing value list"
      ) ? ;
      self.tag( "define-fun" ) ? ;
      let expr = parser.parse_expr( self, info.clone() ) ? ;
      let value = parser.parse_value(self) ? ;
      values.push( (expr, value) ) ;
      self.tag(")") ? ;
    }
    self.clear() ;
    Ok(values)
  }

}


/// Can parse identifiers and types. Used for `get_model`.
///
/// For more information refer to the [module-level documentation].
///
/// [module-level documentation]: index.html
pub trait IdentParser<'a, Ident, Type, Input>: Copy {
  fn parse_ident(self, Input) -> SmtRes<Ident> ;
  fn parse_type(self, Input) -> SmtRes<Type> ;
}
impl<'a, Ident, Type, T> IdentParser<'a, Ident, Type, & 'a str> for T
where T: IdentParser<'a, Ident, Type, & 'a [u8]> {
  fn parse_ident(self, input: & 'a str) -> SmtRes<Ident> {
    self.parse_ident( input.as_bytes() )
  }
  fn parse_type(self, input: & 'a str) -> SmtRes<Type> {
    self.parse_type( input.as_bytes() )
  }
}
impl<'a, Ident, Type, T, Br> IdentParser<
  'a, Ident, Type, & 'a mut SmtParser<Br>
> for T
where
T: IdentParser<'a, Ident, Type, & 'a str>, Br: BufRead {
  fn parse_ident(self, input: & 'a mut SmtParser<Br>) -> SmtRes<Ident> {
    self.parse_ident( input.get_sexpr() ? )
  }
  fn parse_type(self, input: & 'a mut SmtParser<Br>) -> SmtRes<Type> {
    self.parse_type( input.get_sexpr() ? )
  }
}

/// Can parse values. Used for `get-model` and `get-value`.
///
/// For more information refer to the [module-level documentation].
///
/// [module-level documentation]: index.html
pub trait ValueParser<'a, Value, Input>: Copy {
  fn parse_value(self, Input) -> SmtRes<Value> ;
}
impl<'a, Value, T> ValueParser<'a, Value, & 'a str> for T
where T: ValueParser<'a, Value, & 'a [u8]> {
  fn parse_value(self, input: & 'a str) -> SmtRes<Value> {
    self.parse_value( input.as_bytes() )
  }
}
impl<'a, Value, T, Br> ValueParser<
  'a, Value, & 'a mut SmtParser<Br>
> for T where
T: ValueParser<'a, Value, & 'a str>, Br: BufRead {
  fn parse_value(self, input: & 'a mut SmtParser<Br>) -> SmtRes<Value> {
    self.parse_value( input.get_sexpr() ? )
  }
}

/// Can parse expressions. Used for `get_value`.
///
/// For more information refer to the [module-level documentation].
///
/// [module-level documentation]: index.html
pub trait ExprParser<'a, Expr, Info, Input>: Copy {
  fn parse_expr(self, Input, Info) -> SmtRes<Expr> ;
}
impl<'a, Expr, Info, T> ExprParser<'a, Expr, Info, & 'a str> for T
where T: ExprParser<'a, Expr, Info, & 'a [u8]> {
  fn parse_expr(self, input: & 'a str, info: Info) -> SmtRes<Expr> {
    self.parse_expr( input.as_bytes(), info )
  }
}
impl<'a, Expr, Info, T, Br> ExprParser<
  'a, Expr, Info, & 'a mut SmtParser<Br>
> for T
where T: ExprParser<'a, Expr, Info, & 'a str>, Br: BufRead {
  fn parse_expr(
    self, input: & 'a mut SmtParser<Br>, info: Info
  ) -> SmtRes<Expr> {
    self.parse_expr( input.get_sexpr() ?, info )
  }
}

/// Can parse proofs. Currenly unused.
///
/// For more information refer to the [module-level documentation].
///
/// [module-level documentation]: index.html
pub trait ProofParser<'a, Proof, Input>: Copy {
  fn parse_proof(self, Input) -> SmtRes<Proof> ;
}
impl<'a, Proof, T> ProofParser<'a, Proof, & 'a str> for T
where T: ProofParser<'a, Proof, & 'a [u8]> {
  fn parse_proof(self, input: & 'a str) -> SmtRes<Proof> {
    self.parse_proof( input.as_bytes() )
  }
}
impl<'a, Proof, T, Br> ProofParser<
  'a, Proof, & 'a mut SmtParser<Br>
> for T
where T: ProofParser<'a, Proof, & 'a str>, Br: BufRead {
  fn parse_proof(self, input: & 'a mut SmtParser<Br>) -> SmtRes<Proof> {
    self.parse_proof( input.get_sexpr() ? )
  }
}
