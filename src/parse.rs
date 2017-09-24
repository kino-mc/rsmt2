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
//! [nom]: https://crates.io/crates/nom (nom crate on crates.io)
//! [regex]: https://crates.io/crates/regex (regex crate on crates.io)
//! [parser]: struct.SmtParser.html (rsmt2's internal parser)

use errors::* ;

use std::io::{ BufRead, BufReader } ;

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
      buff: String::with_capacity(10_000),
      buff_2: String::with_capacity(10_000),
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
  /// Immutable access to the cursor.
  pub fn cursor(& self) -> usize {
    self.cursor
  }

  /// Reads a line from the input. Returns `true` if something was read.
  fn read_line(& mut self) -> Res<bool> {
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
  fn load_sexpr(& mut self) -> Res<usize> {
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
  pub fn try_tag(& mut self, tag: & str) -> Res<bool> {
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
  pub fn tag(& mut self, tag: & str) -> Res<()> {
    if self.try_tag(tag) ? {
      Ok(())
    } else {
      self.fail_with( format!("expected `{}`", tag) )
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
  pub fn try_word(& mut self, word: & str) -> Res<bool> {
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
  pub fn try_tags<'a, Tags, S>(& mut self, tags: & 'a Tags) -> Res<bool>
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
  pub fn tags<'a, Tags, S>(& mut self, tags: & 'a Tags) -> Res<()>
  where & 'a Tags: IntoIterator<Item = S>, S: AsRef<str> {
    for tag in tags { self.tag( tag.as_ref() ) ? }
    Ok(())
  }


  /// Generates a failure at the current position.
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
  pub fn try_bool(& mut self) -> Res< Option<bool> > {
    if self.try_word("true") ? {
      Ok( Some(true) )
    } else if self.try_word("false") ? {
      Ok( Some(false) )
    } else {
      Ok( None )
    }
  }

  /// Tries to parse an unsigned integer. Does **not** backtrack (or mark).
  fn try_uint(& mut self) -> Res< Option<& str> > {
    let res = self.get_sexpr() ? ;
    for c in res.chars() {
      if ! c.is_numeric() { return Ok(None) }
    }
    Ok( Some(res) )
  }

  /// Tries to parses an integer. The boolean is `true` iff the integer is
  /// positive.
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
  pub fn try_int<F, T, Err>(& mut self, f: F) -> Res< Option<T> >
  where F: FnOnce(& str, bool) -> Result<T, Err>, Err: ::std::error::Error {
    self.spc_cmt() ;
    self.mark() ;
    let mut res = None ;
    if self.try_tag("(") ? {
      let pos = if self.try_tag("+") ? {
        true
      } else if self.try_tag("-") ? {
        false
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
      self.tag(")") ?
    } else {
      if let Some(uint) = self.try_uint() ? {
        match f(uint, true) {
          Ok(int) => res = Some(int),
          Err(e) => bail!("error parsing integer `{}`: {}", uint, e),
        }
      }
    }
    if res.is_none() { self.backtrack() } else { self.clear_mark() }
    Ok(res)
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
  where
  Parser: for<'a> IdentParser<'a, Ident, Type, & 'a mut Self> +
          for<'a> ValueParser<'a, Value, & 'a mut Self> {
    let mut model = Vec::new() ;
    self.tags( & ["(", "model"] ) ? ;
    while ! self.try_tag(")") ? {
      self.tags( &["(", "define-fun"] ) ? ;
      let id = parser.parse_ident(self) ? ;
      self.tags( & ["(", ")"] ) ? ;
      let typ = parser.parse_type(self) ? ;
      let value = parser.parse_value(self) ? ;
      model.push( (id, typ, value) ) ;
      self.tag(")") ? ;
    }
    self.clear() ;
    Ok(model)
  }


  /// Parses the result of a get-model.
  pub fn get_model<Ident, Value, Type, Parser>(
    & mut self, parser: Parser
  ) -> Res< Vec<(Ident, Vec<Type>, Type, Value)> >
  where
  Parser: for<'a> IdentParser<'a, Ident, Type, & 'a mut Self> +
          for<'a> ValueParser<'a, Value, & 'a mut Self> {
    let mut model = Vec::new() ;
    self.tags( &["(", "model"] ) ? ;
    while ! self.try_tag(")") ? {
      self.tags( &["(", "define-fun"] ) ? ;
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
  ) -> Res< Vec<(Expr, Value)> >
  where
  Parser: for<'a> ValueParser<'a, Value, & 'a mut Self> +
          for<'a> ExprParser<'a, Expr, Info, & 'a mut Self> {
    let mut values = Vec::new() ;
    self.tag("(") ? ;
    while ! self.try_tag(")") ? {
      self.tag("(") ? ;
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
pub trait IdentParser<'a, Ident, Type, Input = & 'a str>: Copy
where Input: ?Sized {
  fn parse_ident(self, Input) -> Res<Ident> ;
  fn parse_type(self, Input) -> Res<Type> ;
}
impl<'a, Ident, Type, T> IdentParser<'a, Ident, Type> for T
where T: IdentParser<'a, Ident, Type, & 'a [u8]> {
  fn parse_ident(self, input: & 'a str) -> Res<Ident> {
    self.parse_ident( input.as_bytes() )
  }
  fn parse_type(self, input: & 'a str) -> Res<Type> {
    self.parse_type( input.as_bytes() )
  }
}
impl<'a, Ident, Type, T, Br> IdentParser<
  'a, Ident, Type, & 'a mut SmtParser<Br>
> for T
where T: IdentParser<'a, Ident, Type, & 'a str>, Br: BufRead {
  fn parse_ident(self, input: & 'a mut SmtParser<Br>) -> Res<Ident> {
    self.parse_ident( input.get_sexpr() ? )
  }
  fn parse_type(self, input: & 'a mut SmtParser<Br>) -> Res<Type> {
    self.parse_type( input.get_sexpr() ? )
  }
}

/// Can parse values. Used for `get-model` and `get-value`.
///
/// For more information refer to the [module-level documentation].
///
/// [module-level documentation]: index.html
pub trait ValueParser<'a, Value, Input = & 'a str>: Copy
where Input: ?Sized {
  fn parse_value(self, Input) -> Res<Value> ;
}
impl<'a, Value, T> ValueParser<'a, Value> for T
where T: ValueParser<'a, Value, & 'a [u8]> {
  fn parse_value(self, input: & 'a str) -> Res<Value> {
    self.parse_value( input.as_bytes() )
  }
}
impl<'a, Value, T, Br> ValueParser<'a, Value, & 'a mut SmtParser<Br>> for T
where T: ValueParser<'a, Value, & 'a str>, Br: BufRead {
  fn parse_value(self, input: & 'a mut SmtParser<Br>) -> Res<Value> {
    self.parse_value( input.get_sexpr() ? )
  }
}

/// Can parse expressions. Used for `get_value`.
///
/// For more information refer to the [module-level documentation].
///
/// [module-level documentation]: index.html
pub trait ExprParser<'a, Expr, Info, Input = & 'a str>: Copy
where Input: ?Sized {
  fn parse_expr(self, Input, Info) -> Res<Expr> ;
}
impl<'a, Expr, Info, T> ExprParser<'a, Expr, Info> for T
where T: ExprParser<'a, Expr, Info, & 'a [u8]> {
  fn parse_expr(self, input: & 'a str, info: Info) -> Res<Expr> {
    self.parse_expr( input.as_bytes(), info )
  }
}
impl<'a, Expr, Info, T, Br> ExprParser<
  'a, Expr, Info, & 'a mut SmtParser<Br>
> for T
where T: ExprParser<'a, Expr, Info, & 'a str>, Br: BufRead {
  fn parse_expr(self, input: & 'a mut SmtParser<Br>, info: Info) -> Res<Expr> {
    self.parse_expr( input.get_sexpr() ?, info )
  }
}

/// Can parse proofs. Currenly unused.
///
/// For more information refer to the [module-level documentation].
///
/// [module-level documentation]: index.html
pub trait ProofParser<'a, Proof, Input = & 'a str>: Copy
where Input: ?Sized {
  fn parse_proof(self, Input) -> Res<Proof> ;
}
impl<'a, Proof, T> ProofParser<'a, Proof> for T
where T: ProofParser<'a, Proof, & 'a [u8]> {
  fn parse_proof(self, input: & 'a str) -> Res<Proof> {
    self.parse_proof( input.as_bytes() )
  }
}
impl<'a, Proof, T, Br> ProofParser<'a, Proof, & 'a mut SmtParser<Br>> for T
where T: ProofParser<'a, Proof, & 'a str>, Br: BufRead {
  fn parse_proof(self, input: & 'a mut SmtParser<Br>) -> Res<Proof> {
    self.parse_proof( input.get_sexpr() ? )
  }
}
