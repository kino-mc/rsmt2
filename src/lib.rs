//! "A wrapper around an SMT Lib 2(.5)-compliant SMT solver.
//! 
//! See [`CHANGES.md`](https://github.com/kino-mc/rsmt2/blob/master/README.md)
//! for the list of changes.
//! 
//! Solvers run in a separate process and communication is achieved *via*
//! system pipes.
//! 
//! This library does **not** have a structure for S-expressions. It should be
//! provided by the user, as well as the relevant printing and parsing
//! functions. Print traits are in the [`to_smt` module][to smt mod], while the
//! parse traits are in the [`parse` module][parse mod].
//! 
//! If you use this library consider contacting us on the
//! [repository](https://github.com/kino-mc/rsmt2) so that we can add your
//! project to the readme.
//! 
//! ## (A)synchronous commands.
//! 
//! The functions corresponding to SMT Lib 2 commands come in two flavors,
//! asynchronous and synchronous.
//! 
//! *Synchronous* means that the command is printed on the solver's stdin, and
//! the result is parsed **right away**. Users get control back whenever the
//! solver is done working and parsing is done. In other words, synchronous
//! commands are *blocking*.
//! 
//! *Asynchronous* means that after the command is printed and control is given
//! back to the user. To retrieve the result, users must call the relevant
//! `parse_...` function. For instance, `parse_sat` for `check_sat`. In other
//! words, `print_` commands are *non-blocking*.
//! 
//! 
//! The example below uses synchronous commands.
//! 
//! 
//! ## Workflow
//! 
//! The workflow is introduced below on a simple example. We first define a few
//! helper types we will use later for the expression type.
//! 
//! ```
//! /// Operators. Just implements `Display`, never manipulated directly by the
//! /// solver.
//! #[derive(Copy, Clone)]
//! pub enum Op {
//!   Add, Sub, Mul, Conj, Disj, Eql, Ge, Gt, Lt, Le,
//! }
//! impl ::std::fmt::Display for Op {
//!   fn fmt(& self, w: & mut ::std::fmt::Formatter) -> ::std::fmt::Result {
//!     w.write_str(
//!       match * self {
//!         Op::Add => "+",
//!         Op::Sub => "-",
//!         Op::Mul => "*",
//!         Op::Conj => "and",
//!         Op::Disj => "or",
//!         Op::Eql => "=",
//!         Op::Ge => ">=",
//!         Op::Gt => ">",
//!         Op::Lt => "<",
//!         Op::Le => "<=",
//!       }
//!     )
//!   }
//! }
//! 
//! 
//! /// A constant.
//! #[derive(Clone, Copy)]
//! pub enum Cst {
//!   /// Boolean constant.
//!   B(bool),
//!   /// Integer constant.
//!   I(isize),
//! }
//! impl ::std::fmt::Display for Cst {
//!   fn fmt(& self, w: & mut ::std::fmt::Formatter) -> ::std::fmt::Result {
//!     match * self {
//!       Cst::B(b) => write!(w, "{}", b),
//!       Cst::I(i) if i >= 0 => write!(w, "{}", i),
//!       Cst::I(i) => write!(w, "(- {})", - i),
//!     }
//!   }
//! }
//! impl From<bool> for Cst {
//!   fn from(b: bool) -> Self {
//!     Cst::B(b)
//!   }
//! }
//! impl From<isize> for Cst {
//!   fn from(i: isize) -> Self {
//!     Cst::I(i)
//!   }
//! }
//! ```
//! 
//! These types are defined in the [`simple_example` module][simple example
//! mod], and will be imported from there in the rest of the explanation. We
//! then define the expression type, and make it implement the [`Expr2Smt`
//! trait][expr 2 smt] that writes it as an SMT-LIB 2 expression in a writer.
//! 
//! ## Print functions
//! 
//! Since the structure for S-expressions is provided by users, they also need
//! to provide functions to print it in SMT Lib 2.
//! 
//! To use all SMT Lib 2 commands in a type-safe manner, the library requires
//! printers over
//! 
//! * sorts: `Sort2Smt` trait (*e.g.* for `declare-fun`),
//! * symbols: `Sym2Smt` trait (*e.g.* for `declare-fun`),
//! * expressions: `Expr2Smt` trait (*e.g.* for `assert`).
//! 
//! All user-provided printing functions take some *information*. That way,
//! users can pass some information to, say, `assert` that can modify printing.
//! This is typically used when dealing with transition systems to perform
//! "print-time unrolling". See the [`example` module][example mod] if you're
//! interested; the example below will not use print-time information.
//! 
//! ```
//! extern crate rsmt2 ;
//! 
//! use rsmt2::to_smt::Expr2Smt ;
//! use rsmt2::SmtRes ;
//! use rsmt2::example::simple::{ Op, Cst } ;
//! 
//! /// An example of expression.
//! pub enum Expr {
//!   /// A constant.
//!   C(Cst),
//!   /// Variable.
//!   V(String),
//!   /// Operator application.
//!   O( Op, Vec<Expr> ),
//! }
//! impl Expr {
//!   pub fn cst<C: Into<Cst>>(c: C) -> Self {
//!     Expr::C( c.into() )
//!   }
//! }
//! impl Expr2Smt<()> for Expr {
//!   fn expr_to_smt2<Writer>(
//!     & self, w: & mut Writer, _: ()
//!   ) -> SmtRes<()>
//!   where Writer: ::std::io::Write {
//!     let mut stack = vec![ (false, vec![self], false) ] ;
//!     while let Some((space, mut to_write, closing_paren)) = stack.pop() {
//!       if let Some(next) = to_write.pop() {
//!         if space {
//!           write!(w, " ") ?
//!         }
//!         // We have something to print, push the rest back.
//!         stack.push((space, to_write, closing_paren)) ;
//!         match * next {
//!           Expr::C(cst) => write!(w, "{}", cst) ?,
//!           Expr::V(ref var) => write!(w, "{}", var) ?,
//!           Expr::O(op, ref sub_terms) => {
//!             write!(w, "({}", op) ? ;
//!             stack.push((true, sub_terms.iter().rev().collect(), true))
//!           },
//!         }
//!       } else {
//!         // No more things to write at this level.
//!         if closing_paren {
//!           write!(w, ")") ?
//!         }
//!       }
//!     }
//!     Ok(())
//!   }
//! }
//! 
//! # fn main() {}
//! ```
//! 
//! For convenience, all the `...2Smt` traits are implemented for `& str`. This
//! is useful for testing and maybe *very* simple application. Here, we won't
//! implement `Sym2Smt` or `Sort2Smt` and rely on `& str` for symbols and
//! sorts. Using a solver then boils down to creating a [`Solver`][solver]
//! which wraps a z3 process and provides most of the SMT-LIB 2.5 commands.
//! 
//! ```
//! extern crate rsmt2 ;
//!
//! use rsmt2::Solver ;
//! use rsmt2::example::simple::{ Op, Cst, Expr } ;
//! # fn main() {
//! 
//! let conf = ::rsmt2::conf::z3() ;
//! 
//! let mut solver = Solver::new(conf, ()).expect(
//!   "could not spawn solver kid"
//! ) ;
//! 
//! let v_1 = "v_1".to_string() ;
//! let v_2 = "v_2".to_string() ;
//! 
//! solver.declare_const( & v_1, & "Bool" ).expect(
//!   "while declaring v_1"
//! ) ;
//! solver.declare_const( & v_2, & "Int" ).expect(
//!   "while declaring v_2"
//! ) ;
//! 
//! let expr = Expr::O(
//!   Op::Disj, vec![
//!     Expr::O(
//!       Op::Ge, vec![ Expr::cst(-7), Expr::V( v_2.clone() ) ]
//!     ),
//!     Expr::V( v_1.clone() )
//!   ]
//! ) ;
//! 
//! solver.assert( & expr ).expect(
//!   "while asserting an expression"
//! ) ;
//! 
//! if solver.check_sat().expect("during check sat") {
//!   ()
//! } else {
//!   panic!("expected sat, got unsat")
//! }
//! 
//! solver.kill().unwrap()
//! # }
//! ```
//! 
//! Note the `unit` parameter that we passed to the `solver` function:
//! `solver(& mut kid, ())`. This is actually the parser the solver should use
//! when it needs to parse values, symbols, types... In the example above, we
//! only asked for the satisfiability of the assertions. If we had asked for a
//! model, the compiler would have complained by saying that our parser `()`
//! does not implement the right parsing traits.
//! 
//! ## The parser
//! 
//! This example will only use `get_model`, which only requires `IdentParser`
//! and `ValueParser`. In most cases, an empty parser `struct` with the right
//! implementations should be enough.
//! 
//! ```
//! # #[macro_use]
//! # extern crate error_chain ;
//! extern crate rsmt2 ;
//! 
//! use rsmt2::SmtRes ;
//! use rsmt2::parse::{ IdentParser, ValueParser } ;
//! use rsmt2::example::simple::Cst ;
//! 
//! /// Empty parser structure, we will not maintain any context.
//! #[derive(Clone, Copy)]
//! pub struct Parser ;
//! impl<'a> IdentParser<String, String, & 'a str> for Parser {
//!   fn parse_ident(self, input: & 'a str) -> SmtRes<String> {
//!     Ok( input.to_string() )
//!   }
//!   fn parse_type(self, input: & 'a str) -> SmtRes<String> {
//!     match input {
//!       "Int" => Ok( "Int".into() ),
//!       "Bool" => Ok( "Bool".into() ),
//!       sort => bail!("unexpected sort `{}`", sort),
//!     }
//!   }
//! }
//! impl<'a> ValueParser<Cst, & 'a str> for Parser {
//!   fn parse_value(self, input: & 'a str) -> SmtRes<Cst> {
//!     match input.trim() {
//!       "true" => Ok( Cst::B(true) ),
//!       "false" => Ok( Cst::B(false) ),
//!       int => {
//!         use std::str::FromStr ;
//!         let s = int.trim() ;
//!         if let Ok(res) = isize::from_str(s) {
//!           return Ok( Cst::I(res) )
//!         } else if s.len() >= 4 {
//!           if & s[0 .. 1] == "("
//!           && & s[s.len() - 1 ..] == ")" {
//!             let s = & s[1 .. s.len() - 1].trim() ;
//!             if & s[0 .. 1] == "-" {
//!               let s = & s[1..].trim() ;
//!               if let Ok(res) = isize::from_str(s) {
//!                 return Ok( Cst::I(- res) )
//!               }
//!             }
//!           }
//!         }
//!         bail!("unexpected value `{}`", int)
//!       },
//!     }
//!   }
//! }
//! # fn main() {}
//! ```
//! 
//! As a side note, it would have been simpler to implement `ValueParser` with
//! a [`& mut SmtParser`][smt parser], as it provides the parsers we needed.
//! 
//! ```
//! 
//! use rsmt2::SmtRes ;
//! use rsmt2::parse::{ SmtParser, IdentParser, ValueParser } ;
//! use rsmt2::example::simple::Cst ;
//! 
//! 
//! #[derive(Clone, Copy)]
//! struct Parser ;
//! impl<'a, Br> ValueParser< Cst, & 'a mut SmtParser<Br> > for Parser
//! where Br: ::std::io::BufRead {
//!   fn parse_value(self, input: & 'a mut SmtParser<Br>) -> SmtRes<Cst> {
//!     use std::str::FromStr ;
//!     if let Some(b) = input.try_bool() ? {
//!       Ok( Cst::B(b) )
//!     } else if let Some(int) = input.try_int(
//!       |int, pos| match isize::from_str(int) {
//!         Ok(int) => if pos { Ok(int) } else { Ok(- int) },
//!         Err(e) => Err(e),
//!       }
//!     ) ? {
//!       Ok( Cst::I(int) )
//!     } else {
//!       input.fail_with("unexpected value")
//!     }
//!   }
//! }
//! ```
//! 
//! Anyway, once we pass `Parser` to the solver creation function, and all
//! conditions are met to ask the solver for a model.
//! 
//! ```
//! # #[macro_use]
//! # extern crate error_chain ;
//! extern crate rsmt2 ;
//! 
//! use rsmt2::{ SmtRes, Solver } ;
//! use rsmt2::conf::z3 ;
//! use rsmt2::example::simple::{
//!   Cst, Op, Expr, Parser
//! } ;
//! 
//! # fn main() {
//! let conf = z3() ;
//! 
//! let mut solver = Solver::new(conf, Parser).expect(
//!   "could not spawn solver kid"
//! ) ;
//!
//! let v_1 = "v_1".to_string() ;
//! let v_2 = "v_2".to_string() ;
//! 
//! solver.declare_const( & v_1, & "Bool" ).expect(
//!   "while declaring v_1"
//! ) ;
//! solver.declare_const( & v_2, & "Int" ).expect(
//!   "while declaring v_2"
//! ) ;
//! 
//! let expr = Expr::O(
//!   Op::Disj, vec![
//!     Expr::O(
//!       Op::Ge, vec![ Expr::cst(-7), Expr::V( v_2.clone() ) ]
//!     ),
//!     Expr::V( v_1.clone() )
//!   ]
//! ) ;
//! 
//! solver.assert( & expr ).expect(
//!   "while asserting an expression"
//! ) ;
//! 
//! if solver.check_sat().expect("during check sat") {
//! 
//!   let model = solver.get_model_const().expect(
//!     "while getting model"
//!   ) ;
//! 
//!   let mut okay = false ;
//!   for (ident, typ, value) in model {
//!     if ident == v_1 {
//!       assert_eq!( typ, "Bool" ) ;
//!       match value {
//!         Cst::B(true) => okay = true,
//!         Cst::B(false) => (),
//!         Cst::I(int) => panic!(
//!           "value for v_1 is `{}`, expected boolean", int
//!         ),
//!       }
//!     } else if ident == v_2 {
//!       assert_eq!( typ, "Int" ) ;
//!       match value {
//!         Cst::I(i) if -7 >= i => okay = true,
//!         Cst::I(_) => (),
//!         Cst::B(b) => panic!(
//!           "value for v_2 is `{}`, expected isize", b
//!         ),
//!       }
//!     }
//!   }
//! 
//!   if ! okay {
//!     panic!("got sat, but model is spurious")
//!   }
//! 
//! } else {
//!   panic!("expected sat, got unsat")
//! }
//! 
//! solver.kill().unwrap()
//! # }
//! ```
//!
//!
//! [solver]: struct.Solver.html (Solver type)
//! [parse mod]: parse/index.html (parse module)
//! [to smt mod]: to_smt/index.html (to_smt module)
//! [smt parser]: parse/struct.SmtParser.html (SmtParser structure)
//! [simple example mod]: example/simple/index.html
//! [expr 2 smt]: to_smt/trait.Expr2Smt.html
//! [example mod]: example/index.html

#[macro_use]
extern crate error_chain ;

/// Errors of this library.
pub mod errors {
  error_chain!{
    types {
      Error, ErrorKind, ResExt, SmtRes ;
    }

    foreign_links {
      Io(::std::io::Error) #[doc = "IO error."] ;
    }

    errors {
      #[doc = "The solver reported `unknown`."]
      Unknown {
        description("smt solver reported `unknown`")
      }
      #[doc = "The solver reported `unsupported`."]
      Unsupported {
        description("unsupported command")
      }

      #[doc = "IO error."]
      IoError(s: String) {
        description("input/output error")
        display("IO error: \"{}\"", s)
      }

      #[doc = "The solver reported an error."]
      SolverError(s: String) {
        description("solver error")
        display("solver error: \"{}\"", s)
      }

      #[doc =
        "Parse error, contains the s-expression on which the error happened"
      ]
      ParseError(msg: String, sexpr: String) {
        description("parse error")
        display("parse error: {} on `{}`", msg, sexpr)
      }
    }
  }
}

#[macro_use]
mod common ;
pub mod conf ;
pub mod parse ;
mod solver ;
pub mod actlit ;

pub use errors::SmtRes ;

pub use common::Logic ;
pub use solver::Solver ;

pub mod example ;

// /// Internal traits used to build solvers.
// pub mod internals {
//   pub use parse::SmtParser ;
//   pub use solver::SolverBasic ;
// }

/// Traits your types must implement so that `rsmt2` can use them.
pub mod to_smt {
  pub use common::{ Expr2Smt, Sort2Smt, Sym2Smt } ;
}

