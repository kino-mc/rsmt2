//! SMT Lib 2 result parsers.
//!
//! Depending on the commands you plan to use, your parser will need to implement
//!
//! |                  | for                                              |
//! |:----------------:|:------------------------------------------------:|
//! | [`IdentParser`] | [`Solver::get_model`](super::Solver::get_model)   |
//! | [`ModelParser`] | [`Solver::get_model`](super::Solver::get_model)   |
//! | [`ValueParser`] | [`Solver::get_model`](super::Solver::get_model)   |
//! | [`ExprParser`]  | [`Solver::get_values`](super::Solver::get_values) |
//! | [`ProofParser`] | *currently unused*                                |
//!
//! You can choose the kind of input you want to parse, between
//!
//! - `& [u8]`, *e.g.* for [`nom`][nom],
//! - `& str`, *e.g.* for [`regex`][regex],
//! - [`& mut SmtParser`](SmtParser), `rmst2`'s own parser which provides simple helpers to parse
//!   s-expressions.
//!
//! The first two are safe in that your parsers will be called on the tokens they are supposed to
//! parse and nothing else.
//!
//!
//! ## Parsing: `&str` (and `&[u8]`)
//!
//!
//! Here is a first example where we defined a value parser that only recognizes booleans, to
//! showcase [`ValueParser`] and [`Solver::get_values`](super::Solver::get_values). `Expr`essions
//! are represented as strings, and `Val`ues are booleans.
//!
//! ```rust
//! # extern crate rsmt2;
//! use rsmt2::{SmtConf, SmtRes, Solver, parse::ValueParser, parse::ExprParser};
//!
//! pub type Expr = String;
//! pub type Val = bool;
//!
//! #[derive(Clone, Copy)]
//! pub struct Parser;
//! // Value parser implementation for `&'a str` input.
//! impl<'a> ValueParser<Val, &'a str> for Parser {
//!     fn parse_value(self, input: &'a str) -> SmtRes<Val> {
//!         // When parsing `&str` or `&[u8]`, the input is the actual value.
//!         match input {
//!             "true" => Ok(true),
//!             "false" => Ok(false),
//!             s => Err(format!("unsupported value `{}`", s).into()),
//!         }
//!     }
//! }
//! impl<'a> ExprParser<Expr, (), &'a str> for Parser {
//!     fn parse_expr(self, input: &'a str, _: ()) -> SmtRes<Expr> {
//!         // When parsing `&str` or `&[u8]`, the input is the actual expression. Here we're not
//!         // constructing some complex expression, we just want to turn the `&str` into a
//!         // `String`.
//!         Ok(input.into())
//!     }
//! }
//!
//! let mut solver = SmtConf::default_z3().spawn(Parser).unwrap();
//! solver.declare_const("a", "Bool").unwrap();
//! solver.declare_const("b", "Bool").unwrap();
//! solver.assert("(and a (not b))").unwrap();
//! let is_sat = solver.check_sat().unwrap();
//! assert!(is_sat);
//! let values = solver.get_values(&["a", "b", "(and a (not b))"]).unwrap();
//! assert_eq!(
//!     &format!("{:?}", values),
//!     r#"[("a", true), ("b", false), ("(and a (not b))", true)]"#
//! );
//! let mut values = values.into_iter();
//! assert_eq!( values.next(), Some(("a".to_string(), true)) );
//! assert_eq!( values.next(), Some(("b".to_string(), false)) );
//! assert_eq!( values.next(), Some(("(and a (not b))".to_string(), true)) );
//! ```
//!
//! Here is a second example where we implement [`ModelParser`] and [`IdentParser`]. We must provide
//! parsing functions for identifiers, types and values.
//!
//! ```rust
//! # extern crate rsmt2;
//! # use rsmt2::parse::SmtParser;
//! # fn main() {
//! use rsmt2::parse::{ IdentParser, ModelParser };
//! use rsmt2::SmtRes;
//! let txt = "\
//!   ( model (define-fun a () Int (- 17)) )
//! ";
//! let mut parser = SmtParser::of_str(txt);
//!
//! struct Parser;
//! impl<'a, 'b> ModelParser<
//!     String, String, String, & 'a str
//! > for & 'b Parser {
//!     fn parse_value(
//!         self, input: & 'a str,
//!         _: & String, _: & [ (String, String) ], _: & String,
//!     ) -> SmtRes<String> {
//!         Ok(input.into())
//!     }
//! }
//! impl<'a, 'b> IdentParser<String, String, & 'a str> for & 'b Parser {
//!     fn parse_ident(self, input: & 'a str) -> SmtRes<String> {
//!         Ok(input.into())
//!     }
//!     fn parse_type(self, input: & 'a str) -> SmtRes<String> {
//!         Ok(input.into())
//!     }
//! }
//!
//! let model = parser.get_model_const( false, & Parser ).expect("model");
//! assert_eq!( model, vec![ ("a".into(), "Int".into(), "(- 17)".into()) ] )
//! # }
//! ```
//!
//!
//! ## Parsing: [`SmtParser`]
//!
//! But a parser taking [`SmtParser`] as input is "unsafe" in the sense that it has access to the
//! whole input. Note that [`SmtParser`] provides helper parsing functions such as
//! [`SmtParser::try_int`] and [`SmtParser::try_sym`].
//!
//! ```
//! # extern crate rsmt2;
//! # use rsmt2::parse::SmtParser;
//! # fn main() {
//! use rsmt2::parse::{ IdentParser, ModelParser };
//! use rsmt2::errors::SmtRes;
//! let txt = "\
//!     ( model (define-fun a () Int (- 17)) )
//! ";
//! let mut parser = SmtParser::of_str(txt);
//!
//! struct Parser;
//! impl<'a, 'b, Br: ::std::io::BufRead> ModelParser<
//!     String, String, String, & 'a mut SmtParser<Br>
//! > for & 'b Parser {
//!     fn parse_value(
//!         self, input: & 'a mut SmtParser<Br>,
//!         _: & String, _: & [ (String, String) ], _: & String,
//!     ) -> SmtRes<String> {
//!         input.tag("(- 17))") ?; Ok( "-17".into() )
//!         //               ^~~~~ eating more input than we should...
//!     }
//! }
//! impl<'a, 'b, Br: ::std::io::BufRead> IdentParser<
//!     String, String, & 'a mut SmtParser<Br>
//! > for & 'b Parser {
//!     fn parse_ident(self, input: & 'a mut SmtParser<Br>) -> SmtRes<String> {
//!         input.tag("a") ?; Ok( "a".into() )
//!     }
//!     fn parse_type(self, input: & 'a mut SmtParser<Br>) -> SmtRes<String> {
//!         input.tag("Int") ?; Ok( "Int".into() )
//!     }
//! }
//!
//! use rsmt2::errors::ErrorKind;
//! match * parser.get_model_const( false, & Parser ).unwrap_err().kind() {
//!     ErrorKind::ParseError(ref msg, ref token) => {
//!         assert_eq!(
//!             msg, "expected `(` opening define-fun or `)` closing model"
//!         );
//!         assert_eq!(token, "eof")
//!     },
//!     ref error => panic!("unexpected error: {}", error)
//! }
//! # }
//! ```
//!
//! [nom]: https://crates.io/crates/nom (nom crate on crates.io)
//! [regex]: https://crates.io/crates/regex (regex crate on crates.io)

use crate::common::*;

use std::io::{BufRead, BufReader, Read};
use std::process::ChildStdout;

/// Alias for the underlying parser.
pub type RSmtParser = SmtParser<BufReader<ChildStdout>>;

/// Tries a user parser.
macro_rules! try_apply {
    ($e:expr => |$res:pat| $do:expr, $msg:expr) => {
        match $e {
            Ok($res) => $do,
            Err(e) => bail!("{}: {}", $msg, e),
        }
    };
}

/// SMT-LIB 2.0 parser.
pub struct SmtParser<R> {
    /// Reader being parsed.
    input: R,
    /// Buffer we are reading to.
    buff: String,
    /// Second buffer for swapping.
    buff_2: String,
    /// Current position in the text.
    cursor: usize,
}

impl<R: Read> Read for SmtParser<R> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.input.read(buf)
    }
}

impl<'a> SmtParser<BufReader<&'a [u8]>> {
    /// Constructor from a string, mostly for doc/test purposes.
    pub fn of_str(s: &'a str) -> Self {
        SmtParser::new(BufReader::new(s.as_bytes()))
    }
}
impl<R: BufRead> SmtParser<R> {
    /// Creates an SMT parser.
    pub fn new(input: R) -> Self {
        SmtParser {
            input,
            buff: String::with_capacity(5_000),
            buff_2: String::with_capacity(5_000),
            cursor: 0,
        }
    }

    /// Swaps the input source.
    pub fn swap(&mut self, nu_input: &mut R) {
        ::std::mem::swap(&mut self.input, nu_input)
    }

    /// Immutable access to the buffer.
    pub fn buff(&self) -> &str {
        &self.buff
    }
    /// Immutable access to the part of the buffer that's not been parsed yet.
    pub fn buff_rest(&self) -> &str {
        &self.buff[self.cursor..]
    }
    /// The current position in the buffer.
    pub fn cursor(&self) -> usize {
        self.cursor
    }

    /// Reads a line from the input. Returns `true` if something was read.
    fn read_line(&mut self) -> SmtRes<bool> {
        let read = self.input.read_line(&mut self.buff)?;
        Ok(read != 0)
    }

    /// Returns the next s-expression and positions the cursor directly after it.
    ///
    /// An s-expression is an ident, a constant with no parens (`42`, `false`, *etc.*), or something
    /// between (nested) parens.
    ///
    /// ```
    /// # extern crate rsmt2;
    /// # use rsmt2::parse::SmtParser;
    /// # fn main() {
    /// let txt = "\
    ///     token ; a comment\n\n next_token; more comments\n\
    ///     (+ |quoted ident,; a comment\n parens don't count)| 7)42 false\
    /// ";
    /// let mut parser = SmtParser::of_str(txt);
    ///
    /// assert_eq!( parser.get_sexpr().unwrap(), "token" );
    /// assert_eq!( parser.buff_rest(), " ; a comment\n" );
    ///
    /// assert_eq!( parser.get_sexpr().unwrap(), "next_token" );
    /// assert_eq!( parser.buff_rest(), "; more comments\n" );
    ///
    /// assert_eq!(
    ///     parser.get_sexpr().unwrap(),
    ///     "(+ |quoted ident,; a comment\n parens don't count)| 7)"
    /// );
    /// assert_eq!( parser.buff_rest(), "42 false" );
    ///
    /// assert_eq!( parser.get_sexpr().unwrap(), "42" );
    /// assert_eq!( parser.buff_rest(), " false" );
    ///
    /// assert_eq!( parser.get_sexpr().unwrap(), "false" );
    /// assert_eq!( parser.buff_rest(), "" );
    /// # }
    /// ```
    pub fn get_sexpr(&mut self) -> SmtRes<&str> {
        let sexpr_end = self.load_sexpr()?;
        let sexpr_start = self.cursor;
        self.cursor = sexpr_end;
        Ok(&self.buff[sexpr_start..sexpr_end])
    }

    /// Loads lines until a full s-expr is loaded.
    ///
    /// Returns the next position of the end of the sexpr. The cursor will be set at its beginning.
    fn load_sexpr(&mut self) -> SmtRes<usize> {
        self.spc_cmt();

        let (mut op_paren, mut cl_paren) = (0, 0);
        let mut quoted_ident = false;
        let mut sexpr_start = self.cursor;
        let mut sexpr_end = sexpr_start;

        'load: loop {
            if sexpr_start == self.buff.len() {
                let eof = !self.read_line()?;
                if eof {
                    bail!("reached eof")
                }
            }
            debug_assert!(op_paren >= cl_paren);

            for line in self.buff[sexpr_start..].lines() {
                debug_assert!(op_paren >= cl_paren);

                let mut this_end = sexpr_start;
                let mut chars = line.chars();
                'this_line: while let Some(c) = chars.next() {
                    debug_assert!(op_paren >= cl_paren);
                    this_end += 1;

                    if quoted_ident {
                        quoted_ident = c != '|';
                        if !quoted_ident && op_paren == 0 {
                            sexpr_end = this_end;
                            break 'load;
                        }
                    } else {
                        match c {
                            ';' => break 'this_line,
                            '|' => quoted_ident = !quoted_ident,
                            '(' => op_paren += 1,
                            ')' => {
                                cl_paren += 1;
                                if op_paren == cl_paren {
                                    sexpr_end = this_end;
                                    break 'load;
                                }
                            }
                            _ => {
                                if !c.is_whitespace() && op_paren == 0 {
                                    // print!("... `");
                                    'token: for c in chars {
                                        if c.is_whitespace() {
                                            break 'token;
                                        }
                                        match c {
                                            ')' | '(' | '|' | ';' => break 'token,
                                            _ => this_end += 1,
                                        }
                                    }
                                    sexpr_end = this_end;
                                    break 'load;
                                }
                            }
                        }
                    }
                }
            }
            if sexpr_start == self.buff.len() {
                break 'load;
            }
            sexpr_start = self.buff.len()
        }

        self.spc_cmt();
        Ok(sexpr_end)
    }

    /// Clears the buffer up to the current position.
    pub fn clear(&mut self) {
        self.spc_cmt();
        if !self.cursor >= self.buff.len() {
            debug_assert!(self.buff_2.is_empty());
            self.buff_2.push_str(&self.buff[self.cursor..]);
            self.buff.clear();
            ::std::mem::swap(&mut self.buff, &mut self.buff_2);
            self.cursor = 0
        } else {
            self.buff.clear();
            self.cursor = 0
        }
    }

    /// Prints itself, for debugging.
    pub fn print(&self, pref: &str) {
        let mut count = 0;
        let mut printed_cursor = false;
        for line in self.buff.lines() {
            println!("{}|`{}`", pref, line);
            if !printed_cursor {
                let nu_count = count + line.len() + 1;
                if self.cursor <= nu_count {
                    printed_cursor = true;
                    println!("{0}| {1: >2$}^", pref, "", self.cursor - count)
                }
                count = nu_count;
            }
        }
    }

    /// Parses some spaces or some comments.
    ///
    /// Parsing a tag or loading an s-expression fetches new lines, this does not.
    ///
    /// ```
    /// # extern crate rsmt2;
    /// # use rsmt2::parse::SmtParser;
    /// # fn main() {
    /// let txt = "  token ; a comment\n\n next token; last comment";
    /// let mut parser = SmtParser::of_str(txt);
    ///
    /// parser.spc_cmt();
    /// assert_eq!( parser.buff_rest(), "" );
    /// assert_eq!( parser.buff(), "" );
    ///
    /// assert!( parser.try_tag("token").expect("token") );
    /// assert_eq!( parser.buff_rest(), " ; a comment\n" );
    /// assert_eq!( parser.buff(), "  token ; a comment\n" );
    ///
    /// parser.spc_cmt();
    /// assert_eq!( parser.buff_rest(), "" );
    /// assert_eq!( parser.buff(), "  token ; a comment\n" );
    ///
    /// assert!( parser.try_tag("next token").expect("token") );
    /// assert_eq!( parser.buff_rest(), "; last comment" );
    /// assert_eq!( parser.buff(), txt );
    ///
    /// parser.spc_cmt();
    /// assert_eq!( parser.buff_rest(), "" );
    /// assert_eq!( parser.buff(), txt );
    /// # }
    /// ```
    pub fn spc_cmt(&mut self) {
        let mut chars = self.buff[self.cursor..].chars();
        'spc_cmt: while let Some(c) = chars.next() {
            if !c.is_whitespace() {
                if c == ';' {
                    self.cursor += 1;
                    'skip_line: while let Some(c) = chars.next() {
                        self.cursor += 1;
                        if c == '\n' || c == '\r' {
                            break 'skip_line;
                        }
                    }
                } else {
                    break 'spc_cmt;
                }
            } else {
                self.cursor += 1;
            }
        }
    }

    /// Tries to parse a tag, `true` if successful. Parse whitespaces and comments if any before the
    /// token.
    ///
    /// If this function returns `false`, then the cursor is at the first non-whitespace
    /// non-commented character after the original cursor position.
    ///
    /// See also [`Self::tag`], [`Self::tag_info`] and [`Self::tags`].
    ///
    /// ```
    /// # extern crate rsmt2;
    /// # use rsmt2::parse::SmtParser;
    /// # fn main() {
    /// let txt = "\
    ///   a tag is anything  |(>_<)| ; a comment\n\n next token; last comment\
    /// ";
    /// let mut parser = SmtParser::of_str(txt);
    /// assert!( parser.try_tag("a tag is anything").expect("tag") );
    /// assert_eq!( parser.buff_rest(), "  |(>_<)| ; a comment\n" );
    /// assert!( ! parser.try_tag("not the token").expect("tag") );
    /// assert_eq!( parser.buff_rest(), "|(>_<)| ; a comment\n" );
    /// assert!( parser.try_tag("|(>_<)|").expect("tag") );
    /// assert!( ! parser.try_tag("not the next token").expect("tag") );
    /// assert_eq!( parser.buff_rest(), "next token; last comment" );
    /// assert!( parser.try_tag("next token").expect("tag") );
    /// # }
    /// ```
    pub fn try_tag(&mut self, tag: &str) -> SmtRes<bool> {
        loop {
            self.spc_cmt();
            if self.cursor + tag.len() >= self.buff.len() + 1 {
                if self.cursor < self.buff.len() {
                    if self.buff[self.cursor..self.buff.len()]
                        != tag[0..self.buff.len() - self.cursor]
                    {
                        return Ok(false);
                    } else {
                        ()
                    }
                }
                let eof = !self.read_line()?;
                self.spc_cmt();
                if eof {
                    return Ok(false);
                }
            } else if &self.buff[self.cursor..self.cursor + tag.len()] == tag {
                self.cursor += tag.len();
                return Ok(true);
            } else {
                self.spc_cmt();
                return Ok(false);
            }
        }
    }
    /// Parses a tag or fails.
    ///
    /// Returns `()` exactly when [`Self::try_tag`] returns `true`, and an error otherwise.
    pub fn tag(&mut self, tag: &str) -> SmtRes<()> {
        if self.try_tag(tag)? {
            Ok(())
        } else {
            self.fail_with(format!("expected `{}`", tag))
        }
    }
    /// Parses a tag or fails, appends `err_msg` at the end of the error message.
    ///
    /// Returns `()` exactly when [`Self::try_tag`] returns `true`, and an error otherwise.
    pub fn tag_info(&mut self, tag: &str, err_msg: &str) -> SmtRes<()> {
        if self.try_tag(tag)? {
            Ok(())
        } else {
            self.fail_with(format!("expected `{}` {}", tag, err_msg))
        }
    }

    /// The current position.
    fn pos(&self) -> usize {
        self.cursor
    }
    /// Backtracks to the position specified.
    fn backtrack_to(&mut self, pos: usize) {
        self.cursor = pos
    }

    /// Parses a tag followed by a whitespace, a paren or a comment.
    ///
    /// If this function returns `false`, then the cursor is at the first non-whitespace
    /// non-commented character after the original cursor position.
    ///
    /// ```
    /// # extern crate rsmt2;
    /// # use rsmt2::parse::SmtParser;
    /// # fn main() {
    /// let txt = "\
    ///   a word is anything  |(>_<)|  last; comment\
    /// ";
    /// let mut parser = SmtParser::of_str(txt);
    /// assert!( parser.try_word("a word is").expect("word") );
    /// assert_eq!( parser.buff_rest(), " anything  |(>_<)|  last; comment" );
    /// assert!( ! parser.try_word("a").expect("word") );
    /// assert_eq!( parser.buff_rest(), "anything  |(>_<)|  last; comment" );
    /// assert!( ! parser.try_word("any").expect("word") );
    /// assert_eq!( parser.buff_rest(), "anything  |(>_<)|  last; comment" );
    /// assert!( ! parser.try_word("anythin").expect("word") );
    /// assert_eq!( parser.buff_rest(), "anything  |(>_<)|  last; comment" );
    /// assert!( parser.try_word("anything").expect("word") );
    /// assert_eq!( parser.buff_rest(), "  |(>_<)|  last; comment" );
    /// assert!( parser.try_word("|").expect("word") );
    /// assert_eq!( parser.buff_rest(), "(>_<)|  last; comment" );
    /// assert!( parser.try_tag("(").expect("tag") );
    /// assert_eq!( parser.buff_rest(), ">_<)|  last; comment" );
    /// assert!( parser.try_word(">_<").expect("word") );
    /// assert_eq!( parser.buff_rest(), ")|  last; comment" );
    /// assert!( parser.try_tag(")").expect("tag") );
    /// assert_eq!( parser.buff_rest(), "|  last; comment" );
    /// assert!( parser.try_word("|").expect("word") );
    /// assert_eq!( parser.buff_rest(), "  last; comment" );
    /// assert!( parser.try_word("last").expect("word") );
    /// assert_eq!( parser.buff_rest(), "; comment" );
    /// # }
    /// ```
    pub fn try_word(&mut self, word: &str) -> SmtRes<bool> {
        let start_pos = self.pos();
        if self.try_tag(word)? {
            if let Some(c) = self.buff[self.cursor..].chars().next() {
                if c.is_whitespace() || c == ')' || c == '(' || c == ';' {
                    return Ok(true);
                }
            }
        }
        self.backtrack_to(start_pos);
        self.spc_cmt();
        Ok(false)
    }

    /// Tries to parse a sequence of things potentially separated by whitespaces and/or comments.
    ///
    /// If this function returns `false`, then the cursor is at the first non-whitespace
    /// non-commented character after the original cursor position.
    ///
    /// ```
    /// # extern crate rsmt2;
    /// # use rsmt2::parse::SmtParser;
    /// # fn main() {
    /// let txt = "\
    ///     a tag is anything  |(>_<)| ; a comment\n\n next token; last comment\
    /// ";
    /// let mut parser = SmtParser::of_str(txt);
    /// assert!(
    ///     parser.try_tags(
    ///         &[ "a", "tag", "is anything", "|", "(", ">_<", ")", "|" ]
    ///     ).expect("tags")
    /// );
    /// assert_eq!( parser.buff_rest(), " ; a comment\n" );
    /// assert!(
    ///     ! parser.try_tags(
    ///         & [ "next", "token", "something else?" ]
    ///     ).expect("tags")
    /// );
    /// assert_eq!( parser.buff_rest(), "next token; last comment" )
    /// # }
    /// ```
    pub fn try_tags<'a, Tags, S>(&mut self, tags: &'a Tags) -> SmtRes<bool>
    where
        &'a Tags: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        let start_pos = self.pos();
        for tag in tags {
            if !self.try_tag(tag.as_ref())? {
                self.backtrack_to(start_pos);
                self.spc_cmt();
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Parses a sequence of things potentially separated by whitespaces and/or comments.
    ///
    /// Returns `()` exactly when [`Self::try_tags`] returns `true`, and an error otherwise.
    pub fn tags<'a, Tags, S>(&mut self, tags: &'a Tags) -> SmtRes<()>
    where
        &'a Tags: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        for tag in tags {
            self.tag(tag.as_ref())?
        }
        Ok(())
    }

    /// Generates a failure at the current position.
    pub fn fail_with<T, Str: Into<String>>(&mut self, msg: Str) -> SmtRes<T> {
        self.try_error()?;
        let sexpr = match self.get_sexpr() {
            Ok(e) => Some(e.to_string()),
            _ => None,
        };
        let sexpr = if let Some(e) = sexpr {
            e
        } else if self.cursor < self.buff.len() {
            let mut stuff = self.buff[self.cursor..].trim().split_whitespace();
            if let Some(stuff) = stuff.next() {
                stuff.to_string()
            } else {
                " ".to_string()
            }
        } else {
            "eof".to_string()
        };
        if sexpr == "unsupported" {
            bail!(ErrorKind::Unsupported)
        } else {
            bail!(ErrorKind::ParseError(msg.into(), sexpr))
        }
    }

    /// Tries to parse a boolean.
    ///
    /// ```
    /// # extern crate rsmt2;
    /// # use rsmt2::parse::SmtParser;
    /// # fn main() {
    /// let txt = "\
    ///     true fls  true_ly_bad_ident false; comment\
    /// ";
    /// let mut parser = SmtParser::of_str(txt);
    /// assert_eq!( parser.try_bool().expect("bool"), Some(true) );
    /// assert_eq!(
    ///     parser.buff_rest(), " fls  true_ly_bad_ident false; comment"
    /// );
    /// assert_eq!( parser.try_bool().expect("bool"), None );
    /// assert_eq!(
    ///     parser.buff_rest(), "fls  true_ly_bad_ident false; comment"
    /// );
    /// parser.tag("fls").expect("tag");
    /// assert_eq!( parser.try_bool().expect("bool"), None );
    /// assert_eq!(
    ///     parser.buff_rest(), "true_ly_bad_ident false; comment"
    /// );
    /// parser.tag("true_ly_bad_ident").expect("tag");
    /// assert_eq!( parser.try_bool().expect("bool"), Some(false) );
    /// assert_eq!(
    ///     parser.buff_rest(), "; comment"
    /// );
    /// # }
    /// ```
    pub fn try_bool(&mut self) -> SmtRes<Option<bool>> {
        if self.try_word("true")? {
            Ok(Some(true))
        } else if self.try_word("false")? {
            Ok(Some(false))
        } else {
            Ok(None)
        }
    }

    /// Parses a boolean or fails.
    pub fn bool(&mut self) -> SmtRes<bool> {
        if let Some(b) = self.try_bool()? {
            Ok(b)
        } else {
            self.fail_with("expected boolean")
        }
    }

    /// Tries to parse an unsigned integer. Does **not** load, backtrack, or mark.
    ///
    /// Returns start and end positions.
    #[inline]
    fn try_uint_indices(&self) -> SmtRes<Option<(usize, usize)>> {
        let mut end = self.cursor;
        let (mut zero_first, mut first) = (false, true);
        for c in self.buff[self.cursor..].chars() {
            if c.is_numeric() {
                if first {
                    first = false;
                    if c == '0' {
                        zero_first = true
                    }
                } else if zero_first {
                    return Ok(None);
                }
                end += 1
            } else {
                break;
            }
        }
        if end > self.cursor {
            Ok(Some((self.cursor, end)))
        } else {
            Ok(None)
        }
    }

    /// Tries to parse an unsigned integer.
    ///
    /// Does **not** load, backtrack, or mark, but moves the cursor to the end of the integer if
    /// any.
    #[inline]
    fn try_uint(&mut self) -> SmtRes<Option<&str>> {
        self.spc_cmt();
        if let Some((res_start, res_end)) = self.try_uint_indices()? {
            self.cursor = res_end;
            Ok(Some(&self.buff[res_start..res_end]))
        } else {
            Ok(None)
        }
    }
    /// Parses an usigned integer or fails.
    #[inline]
    fn uint<F, T>(&mut self, f: F) -> SmtRes<T>
    where
        F: Fn(&str) -> T,
    {
        if let Some(res) = self.try_uint()?.map(f) {
            Ok(res)
        } else {
            self.fail_with("expected unsigned integer")
        }
    }

    /// Tries to parses an integer.
    ///
    /// Parameters of the input function:
    ///
    /// - the absolute value of the integer parsed,
    /// - positiveness flag: `true` iff the integer is positive.
    ///
    /// **NB**: input function `f` cannot return the input string in any way. Doing so will not
    /// borrow-check and is completely unsafe as the parser can and in general will discard what's
    /// in its buffer once it's parsed.
    ///
    /// Only recognizes integers of the form
    ///
    /// ```bash
    /// int   ::= usize             # Not followed by a '.'
    ///         | '(' '-' usize ')'
    /// usize ::= '0' | [1-9][0-9]*
    /// ```
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate rsmt2;
    /// # use rsmt2::parse::SmtParser;
    /// # fn main() {
    /// use std::str::FromStr;
    /// fn to_int(
    ///     input: & str, positive: bool
    /// ) -> Result<isize, <isize as FromStr>::Err> {
    ///     isize::from_str(input).map(
    ///         |num| if positive { num } else { - num }
    ///     )
    /// }
    /// let txt = "\
    ///     666 (- 11) false; comment\n(+ 31) (= tru)\
    /// ";
    /// let mut parser = SmtParser::of_str(txt);
    /// println!("666");
    /// assert_eq!( parser.try_int(to_int).expect("int"), Some(666) );
    /// assert_eq!(
    ///     parser.buff_rest(), " (- 11) false; comment\n"
    /// );
    ///
    /// println!("- 11");
    /// assert_eq!( parser.try_int(to_int).expect("int"), Some(- 11) );
    /// assert_eq!(
    ///     parser.buff_rest(), " false; comment\n"
    /// );
    ///
    /// assert_eq!( parser.try_int(to_int).expect("int"), None );
    /// parser.tag("false").expect("tag");
    ///
    /// println!("31");
    /// assert_eq!( parser.try_int(to_int).expect("int"), Some(31) );
    /// assert_eq!(
    ///     parser.buff_rest(), " (= tru)"
    /// );
    ///
    /// assert_eq!( parser.try_int(to_int).expect("int"), None );
    ///
    /// let txt = " 7.0 ";
    /// println!("{}", txt);
    /// let mut parser = SmtParser::of_str(txt);
    /// assert_eq!( parser.try_int(to_int).expect("int"), None );
    /// assert_eq!(
    ///     parser.buff_rest(), " 7.0 "
    /// );
    ///
    /// let txt = " 00 ";
    /// println!("{}", txt);
    /// let mut parser = SmtParser::of_str(txt);
    /// assert_eq!( parser.try_int(to_int).expect("int"), None );
    /// assert_eq!(
    ///     parser.buff_rest(), " 00 "
    /// );
    /// # }
    /// ```
    pub fn try_int<F, T, Err>(&mut self, f: F) -> SmtRes<Option<T>>
    where
        F: FnOnce(&str, bool) -> Result<T, Err>,
        Err: ::std::fmt::Display,
    {
        let start_pos = self.pos();
        self.load_sexpr()?;

        let mut res = None;

        if let Some((int_start, int_end)) = self.try_uint_indices()? {
            self.cursor = int_end;
            if self.try_tag(".")? {
                self.backtrack_to(start_pos);
                res = None
            } else {
                self.cursor = int_end;
                let uint = &self.buff[int_start..int_end];
                try_apply!(
                  f(uint, true) => |int| res = Some(int),
                  format!("error parsing integer `{}`", uint)
                )
            }
        } else if self.try_tag("(")? {
            let pos = if self.try_tag("-")? {
                false
            } else if self.try_tag("+")? {
                true
            } else {
                self.backtrack_to(start_pos);
                return Ok(None);
            };
            if let Some(uint) = self.try_uint()? {
                match f(uint, pos) {
                    Ok(int) => res = Some(int),
                    Err(e) => {
                        let uint = if !pos {
                            format!("(- {})", uint)
                        } else {
                            uint.into()
                        };
                        bail!("error parsing integer `{}`: {}", uint, e)
                    }
                }
            }
            if !(res.is_some() && self.try_tag(")")?) {
                self.backtrack_to(start_pos);
                return Ok(None);
            }
        }
        if res.is_none() {
            self.backtrack_to(start_pos)
        }
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
    /// idec  ::= '(' '-' udec '.' usize ')' | udec
    /// udec  ::= usize | usize.0
    /// usize ::= [0-9][0-9]*
    /// ```
    ///
    /// **NB**: input function `f` cannot return the input strings in any way. Doing so will not
    /// borrow-check and is completely unsafe as the parser can and in general will discard what's
    /// in its buffer once it's parsed.
    ///
    /// ```
    /// # extern crate rsmt2;
    /// # use rsmt2::parse::SmtParser;
    /// # fn main() {
    /// use std::str::FromStr;
    /// fn to_rat(
    ///     num: & str, den: & str, positive: bool
    /// ) -> Result<(isize, usize), String> {
    ///     let num = isize::from_str(num).map(
    ///         |num| if positive { num } else { - num }
    ///     ).map_err(|e| format!("{}", e)) ?;
    ///     let den = usize::from_str(den).map_err(|e| format!("{}", e)) ?;
    ///     Ok((num, den))
    /// }
    /// let txt = "\
    ///     0.0 666.0 7.42 (- 11.0) false; comment\n(/ 31 27) (- (/ 63 0)) (= tru)\
    /// ";
    /// let mut parser = SmtParser::of_str(txt);
    /// assert_eq!( parser.try_rat(to_rat).expect("rat"), Some((0, 1)) );
    /// assert_eq!(
    ///     parser.buff_rest(), " 666.0 7.42 (- 11.0) false; comment\n"
    /// );
    /// assert_eq!( parser.try_rat(to_rat).expect("rat"), Some((666, 1)) );
    /// assert_eq!(
    ///     parser.buff_rest(), " 7.42 (- 11.0) false; comment\n"
    /// );
    /// assert_eq!( parser.try_rat(to_rat).expect("rat"), Some((742, 100)) );
    /// assert_eq!(
    ///     parser.buff_rest(), " (- 11.0) false; comment\n"
    /// );
    /// assert_eq!( parser.try_rat(to_rat).expect("rat"), Some((- 11, 1)) );
    /// assert_eq!(
    ///     parser.buff_rest(), " false; comment\n"
    /// );
    /// assert_eq!( parser.try_rat(to_rat).expect("rat"), None );
    /// parser.tag("false").expect("tag");
    /// assert_eq!( parser.try_rat(to_rat).expect("rat"), Some((31, 27)) );
    /// assert_eq!(
    ///     parser.buff_rest(), " (- (/ 63 0)) (= tru)"
    /// );
    /// assert_eq!( parser.try_rat(to_rat).expect("rat"), (Some((- 63, 0))) );
    ///
    /// let txt = " 7 ";
    /// let mut parser = SmtParser::of_str(txt);
    /// assert_eq!( parser.try_rat(to_rat).expect("rat"), None );
    /// assert_eq!(
    ///     parser.buff_rest(), " 7 "
    /// );
    ///
    /// let txt = " (- 7) ";
    /// let mut parser = SmtParser::of_str(txt);
    /// assert_eq!( parser.try_rat(to_rat).expect("rat"), None );
    /// assert_eq!(
    ///     parser.buff_rest(), " (- 7) "
    /// );
    /// # }
    /// ```
    pub fn try_rat<F, T, Err>(&mut self, f: F) -> SmtRes<Option<T>>
    where
        F: Fn(&str, &str, bool) -> Result<T, Err>,
        Err: ::std::fmt::Display,
    {
        let err = "error parsing rational";
        let start_pos = self.pos();
        self.load_sexpr()?;

        let mut res = None;

        let positive = if self.try_tags(&["(", "-"])? {
            self.spc_cmt();
            false
        } else {
            true
        };

        if let Some((fst_start, fst_end)) = self.try_uint_indices()? {
            if fst_end + 1 < self.buff.len() && &self.buff[fst_end..(fst_end + 2)] == ".0" {
                try_apply!(
                  f(
                    & self.buff[ fst_start .. fst_end ], "1", positive
                  ) => |okay| res = Some(okay), err
                );
                self.cursor = fst_end + 2
            } else if fst_end < self.buff.len() && &self.buff[fst_end..(fst_end + 1)] == "." {
                self.cursor = fst_end + 1;
                if let Some((snd_start, snd_end)) = self.try_uint_indices()? {
                    let num = format!(
                        "{}{}",
                        &self.buff[fst_start..fst_end],
                        &self.buff[snd_start..snd_end],
                    );
                    let mut den = String::with_capacity(snd_end - snd_start);
                    den.push('1');
                    for _ in snd_start..snd_end {
                        den.push('0')
                    }
                    try_apply!(
                      f(
                        & num, & den, positive
                      ) => |okay| res = Some(okay), err
                    );
                    self.cursor = snd_end
                } else {
                    bail!("ill-formed rational")
                }
            } else {
                self.backtrack_to(start_pos);
                return Ok(None);
            }
        }

        if res.is_none() {
            if !self.try_tag("(")? {
                self.backtrack_to(start_pos);
                return Ok(None);
            }

            if !self.try_tag("/")? {
                self.backtrack_to(start_pos);
                return Ok(None);
            }

            self.spc_cmt();
            res = if let Some((num_start, num_end)) = self.try_uint_indices()? {
                if num_end + 1 < self.buff.len() && &self.buff[num_end..(num_end + 2)] == ".0" {
                    self.cursor = num_end + 2
                // } else if num_end < self.buff.len()
                // && & self.buff[ num_end .. (num_end + 1) ] == "." {
                //   self.cursor = num_end + 1
                } else {
                    self.cursor = num_end
                }
                self.spc_cmt();
                if let Some((den_start, den_end)) = self.try_uint_indices()? {
                    let not_eof = den_end + 1 < self.buff.len();
                    let point_zero = &self.buff[den_end..(den_end + 2)] == ".0";
                    if not_eof && point_zero {
                        self.cursor = den_end + 2
                    // } else if den_end < self.buff.len()
                    // && & self.buff[ den_end .. (den_end + 1) ] == "." {
                    //   self.cursor = den_end + 1
                    } else {
                        self.cursor = den_end
                    }
                    match f(
                        &self.buff[num_start..num_end],
                        &self.buff[den_start..den_end],
                        positive,
                    ) {
                        Ok(res) => Some(res),
                        Err(e) => bail!("error parsing rational: {}", e),
                    }
                } else {
                    None
                }
            } else {
                None
            };

            if res.is_some() {
                self.tag(")")?
            }
        }

        if res.is_some() {
            if !positive {
                self.tag(")")?
            }
            Ok(res)
        } else {
            Ok(None)
        }
    }

    /// Tries to parse a symbol.
    ///
    /// Quoted symbols (anything but `|` surrounded by `|`) are passed **with** the surrounding `|`.
    ///
    /// **NB**: input function `f` cannot return the input string in any way. Doing so will not
    /// borrow-check and is completely unsafe as the parser can and in general will discard what's
    /// in its buffer once it's parsed.
    ///
    /// ```
    /// # extern crate rsmt2;
    /// # use rsmt2::parse::SmtParser;
    /// # fn main() {
    /// fn sym(input: & str) -> Result<String, String> {
    ///     Ok( input.into() )
    /// }
    /// let txt = "\
    ///     ident (- 11) +~stuff; comment\n |some stuff \n [{}!+)(}|\
    /// ";
    /// let mut parser = SmtParser::of_str(txt);
    /// assert_eq!( parser.try_sym(sym).expect("sym"), Some("ident".into()) );
    /// assert_eq!(
    ///     parser.buff_rest(), " (- 11) +~stuff; comment\n"
    /// );
    /// assert_eq!( parser.try_sym(sym).expect("sym"), None );
    /// assert_eq!(
    ///     parser.buff_rest(), "(- 11) +~stuff; comment\n"
    /// );
    /// parser.tag("(- 11)").expect("tag");
    /// assert_eq!( parser.try_sym(sym).expect("sym"), Some("+~stuff".into()) );
    /// assert_eq!(
    ///     parser.buff_rest(), "; comment\n"
    /// );
    /// assert_eq!(
    ///     parser.try_sym(sym).expect("sym"),
    ///     Some("|some stuff \n [{}!+)(}|".into())
    /// );
    /// # }
    /// ```
    pub fn try_sym<F, T, Err>(&mut self, f: F) -> SmtRes<Option<T>>
    where
        F: FnOnce(&str) -> Result<T, Err>,
        Err: ::std::fmt::Display,
    {
        self.spc_cmt();
        let err_end = self.load_sexpr()?;
        let is_sym = if let Some(c) = self.buff[self.cursor..].chars().next() {
            match c {
                _ if c.is_alphabetic() => true,
                '|' | '~' | '!' | '@' | '$' | '%' | '^' | '&' | '*' | '_' | '-' | '+' | '='
                | '<' | '>' | '.' | '?' => true,
                _ => false,
            }
        } else {
            false
        };
        if is_sym {
            let ident = &self.buff[self.cursor..err_end];
            self.cursor = err_end;
            match f(ident) {
                Ok(res) => Ok(Some(res)),
                Err(e) => bail!(
                    "error parsing symbol `{}`: {}",
                    &self.buff[self.cursor..err_end],
                    e
                ),
            }
        } else {
            Ok(None)
        }
    }

    /// Parses `success`.
    pub fn success(&mut self) -> SmtRes<()> {
        self.tag("success")
    }

    /// Parses an error.
    ///
    /// Returns `Ok(())` if no error was parsed, an error otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate rsmt2;
    /// # use rsmt2::parse::SmtParser;
    /// # fn main() {
    /// use rsmt2::parse::{ IdentParser, ValueParser };
    /// use rsmt2::SmtRes;
    /// let txt = "\
    ///     ( error \"huge panic\" )
    /// ";
    /// let mut parser = SmtParser::of_str(txt);
    /// if let Err(e) = parser.try_error() {
    /// #    for e in e.iter() {
    /// #        for line in format!("{}", e).lines() {
    /// #            println!("{}", line)
    /// #        }
    /// #    }
    ///     assert_eq! { & format!("{}", e), "solver error: \"huge panic\"" }
    /// } else {
    ///     panic!("expected error, got nothing :(")
    /// }
    /// # }
    /// ```
    pub fn try_error(&mut self) -> SmtRes<()> {
        let start_pos = self.pos();
        if self.try_tag("(")? {
            self.spc_cmt();
            if self.try_tag("error")? {
                self.spc_cmt();
                if self.try_tag("\"")? {
                    let err_start = self.pos();
                    let mut err_end = err_start;
                    loop {
                        if err_end < self.buff.len() && &self.buff[err_end..err_end + 1] != "\"" {
                            err_end += 1
                        } else {
                            break;
                        }
                    }
                    self.cursor = err_end + 1;
                    self.spc_cmt();
                    self.tag(")").chain_err(|| "closing error message")?;
                    bail!(ErrorKind::SolverError(self.buff[err_start..err_end].into()))
                }
            }
            self.backtrack_to(start_pos)
        }
        Ok(())
    }

    /// Parses the result of a check-sat.
    ///
    /// Returns `None` if the solver reported `unknown`.
    pub fn check_sat(&mut self) -> SmtRes<Option<bool>> {
        self.spc_cmt();
        if self.try_tag("sat")? {
            Ok(Some(true))
        } else if self.try_tag("unsat")? {
            Ok(Some(false))
        } else if self.try_tag("unknown")? {
            Ok(None)
        } else if self.try_tag("timeout")? {
            bail!(ErrorKind::Timeout)
        } else {
            self.try_error()?;
            self.fail_with("expected `sat` or `unsat`")
        }
    }

    /// Tries to parse a reserved actlit id.
    pub fn try_actlit_id(&mut self) -> SmtRes<bool> {
        if self.try_tag(crate::solver::ACTLIT_PREF)? {
            self.uint(|_| ())
                .chain_err(|| "while parsing internal actlit identifier")?;
            self.tag(crate::solver::ACTLIT_SUFF)?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Parses the result of a get-model where all symbols are nullary.
    pub fn get_model_const<Ident, Value, Type, Parser>(
        &mut self,
        prune_actlits: bool,
        parser: Parser,
    ) -> SmtRes<Vec<(Ident, Type, Value)>>
    where
        Parser: for<'a> IdentParser<Ident, Type, &'a mut Self>
            + for<'a> ModelParser<Ident, Type, Value, &'a mut Self>,
    {
        self.spc_cmt();
        self.try_error()?;
        let mut model = Vec::new();
        self.tags(&["(", "model"])?;
        while !self.try_tag(")")? {
            self.tag_info("(", "opening define-fun or `)` closing model")?;
            self.tag("define-fun")?;

            if prune_actlits && self.try_actlit_id()? {
                self.tags(&["(", ")"])?;
                self.tag("Bool")?;
                self.bool()?;
            } else {
                let id = parser.parse_ident(self)?;
                self.tags(&["(", ")"])?;
                let typ = parser.parse_type(self)?;
                let value = parser.parse_value(self, &id, &[], &typ)?;
                model.push((id, typ, value));
            }
            self.tag(")")?
        }
        self.clear();
        Ok(model)
    }

    /// Parses the result of a get-model.
    pub fn get_model<Ident, Value, Type, Parser>(
        &mut self,
        prune_actlits: bool,
        parser: Parser,
    ) -> SmtRes<Model<Ident, Type, Value>>
    where
        Parser: for<'a> IdentParser<Ident, Type, &'a mut Self>
            + for<'a> ModelParser<Ident, Type, Value, &'a mut Self>,
    {
        self.spc_cmt();
        self.try_error()?;
        let mut model = Vec::new();
        self.tags(&["(", "model"])?;
        while !self.try_tag(")")? {
            self.tag_info("(", "opening define-fun or `)` closing model")?;
            self.tag("define-fun")?;

            if prune_actlits && self.try_actlit_id()? {
                self.tags(&["(", ")"])?;
                self.tag("Bool")?;
                self.bool()?;
            } else {
                let id = parser.parse_ident(self)?;
                self.tag("(")?;
                let mut args = Vec::new();
                while self.try_tag("(")? {
                    self.spc_cmt();
                    let id = parser.parse_ident(self)?;
                    self.spc_cmt();
                    let typ = parser.parse_type(self)?;
                    self.spc_cmt();
                    self.tag(")")?;
                    args.push((id, typ))
                }
                self.tag(")")?;
                self.spc_cmt();
                let typ = parser.parse_type(self)?;
                self.spc_cmt();
                let value = parser.parse_value(self, &id, &args, &typ)?;
                model.push((id, args, typ, value));
            }
            self.tag(")")?;
        }
        self.clear();
        Ok(model)
    }

    /// Parses the result of a get-value.
    pub fn get_values<Val, Info: Clone, Expr, Parser>(
        &mut self,
        parser: Parser,
        info: Info,
    ) -> SmtRes<Vec<(Expr, Val)>>
    where
        Parser:
            for<'a> ValueParser<Val, &'a mut Self> + for<'a> ExprParser<Expr, Info, &'a mut Self>,
    {
        self.spc_cmt();
        self.try_error()?;
        let mut values = Vec::new();
        self.tag("(")?;
        while !self.try_tag(")")? {
            self.tag_info("(", "opening expr/value pair or `)` closing value list")?;
            let expr = parser.parse_expr(self, info.clone())?;
            let value = parser.parse_value(self)?;
            values.push((expr, value));
            self.tag(")")?;
        }
        self.clear();
        Ok(values)
    }
}

/// Can parse identifiers and types. Used for `get_model`.
///
/// For more information refer to the [module-level documentation](self).
pub trait IdentParser<Ident, Type, Input>: Copy {
    /// Parses an identifier.
    fn parse_ident(self, i: Input) -> SmtRes<Ident>;
    /// Parses a type.
    fn parse_type(self, i: Input) -> SmtRes<Type>;
}
impl<'a, Ident, Type, T> IdentParser<Ident, Type, &'a str> for T
where
    T: IdentParser<Ident, Type, &'a [u8]>,
{
    fn parse_ident(self, input: &'a str) -> SmtRes<Ident> {
        self.parse_ident(input.as_bytes())
    }
    fn parse_type(self, input: &'a str) -> SmtRes<Type> {
        self.parse_type(input.as_bytes())
    }
}
impl<'a, Ident, Type, T, Br> IdentParser<Ident, Type, &'a mut SmtParser<Br>> for T
where
    T: IdentParser<Ident, Type, &'a str>,
    Br: BufRead,
{
    fn parse_ident(self, input: &'a mut SmtParser<Br>) -> SmtRes<Ident> {
        self.parse_ident(input.get_sexpr()?)
    }
    fn parse_type(self, input: &'a mut SmtParser<Br>) -> SmtRes<Type> {
        self.parse_type(input.get_sexpr()?)
    }
}

/// Can parse models. Used for `get-model`.
///
/// For more information refer to the [module-level documentation](self).
pub trait ModelParser<Ident, Type, Value, Input>: Copy {
    /// Parses a value in the context of a `get-model` command.
    ///
    /// When rsmt2 parses a value for some symbol `id` in a model, it will call this function so
    /// that it knows what to construct the value with. Remember that in a model, values are usually
    /// presented as
    ///
    /// ```lisp
    /// (define-fun <symbol> ( (<arg> <arg_sort>) ... ) <out_sort> <value>)
    /// ```
    ///
    /// This function's purpose is to parse `<value>` and construct an actual `Value`, given all the
    /// information preceeding the `<value>` token. So, parameter
    ///
    /// - `i` is the "Text input", the actual value token tree (`<value>`);
    /// - `id` is the symbol (`symbol`) we're parsing the value of;
    /// - `args` is `id`'s "input signature" (`(<arg> <arg_sort>) ...`);
    /// - `out` is `id`'s output sort (`<out_sort>`).
    fn parse_value(self, i: Input, id: &Ident, args: &[(Ident, Type)], out: &Type)
        -> SmtRes<Value>;
}
impl<'a, Ident, Type, Value, T> ModelParser<Ident, Type, Value, &'a str> for T
where
    T: ModelParser<Ident, Type, Value, &'a [u8]>,
{
    fn parse_value(
        self,
        input: &'a str,
        name: &Ident,
        inputs: &[(Ident, Type)],
        output: &Type,
    ) -> SmtRes<Value> {
        self.parse_value(input.as_bytes(), name, inputs, output)
    }
}
impl<'a, Ident, Type, Value, T, Br> ModelParser<Ident, Type, Value, &'a mut SmtParser<Br>> for T
where
    T: ModelParser<Ident, Type, Value, &'a str>,
    Br: BufRead,
{
    fn parse_value(
        self,
        input: &'a mut SmtParser<Br>,
        name: &Ident,
        inputs: &[(Ident, Type)],
        output: &Type,
    ) -> SmtRes<Value> {
        self.parse_value(input.get_sexpr()?, name, inputs, output)
    }
}

/// Can parse values. Used for `get-value`.
///
/// For more information refer to the [module-level documentation](self).
pub trait ValueParser<Value, Input>: Copy {
    /// Parses a plain value.
    fn parse_value(self, i: Input) -> SmtRes<Value>;
}
impl<'a, Value, T> ValueParser<Value, &'a str> for T
where
    T: ValueParser<Value, &'a [u8]>,
{
    fn parse_value(self, input: &'a str) -> SmtRes<Value> {
        self.parse_value(input.as_bytes())
    }
}
impl<'a, Value, T, Br> ValueParser<Value, &'a mut SmtParser<Br>> for T
where
    T: ValueParser<Value, &'a str>,
    Br: BufRead,
{
    fn parse_value(self, input: &'a mut SmtParser<Br>) -> SmtRes<Value> {
        self.parse_value(input.get_sexpr()?)
    }
}

/// Can parse expressions. Used for `get_value`.
///
/// For more information refer to the [module-level documentation](self).
pub trait ExprParser<Expr, Info, Input>: Copy {
    fn parse_expr(self, i: Input, info: Info) -> SmtRes<Expr>;
}
impl<'a, Expr, Info, T> ExprParser<Expr, Info, &'a str> for T
where
    T: ExprParser<Expr, Info, &'a [u8]>,
{
    fn parse_expr(self, input: &'a str, info: Info) -> SmtRes<Expr> {
        self.parse_expr(input.as_bytes(), info)
    }
}
impl<'a, Expr, Info, T, Br> ExprParser<Expr, Info, &'a mut SmtParser<Br>> for T
where
    T: ExprParser<Expr, Info, &'a str>,
    Br: BufRead,
{
    fn parse_expr(self, input: &'a mut SmtParser<Br>, info: Info) -> SmtRes<Expr> {
        self.parse_expr(input.get_sexpr()?, info)
    }
}

/// Can parse proofs. Currenly unused.
///
/// For more information refer to the [module-level documentation](self).
pub trait ProofParser<Proof, Input>: Copy {
    fn parse_proof(self, i: Input) -> SmtRes<Proof>;
}
impl<'a, Proof, T> ProofParser<Proof, &'a str> for T
where
    T: ProofParser<Proof, &'a [u8]>,
{
    fn parse_proof(self, input: &'a str) -> SmtRes<Proof> {
        self.parse_proof(input.as_bytes())
    }
}
impl<'a, Proof, T, Br> ProofParser<Proof, &'a mut SmtParser<Br>> for T
where
    T: ProofParser<Proof, &'a str>,
    Br: BufRead,
{
    fn parse_proof(self, input: &'a mut SmtParser<Br>) -> SmtRes<Proof> {
        self.parse_proof(input.get_sexpr()?)
    }
}
