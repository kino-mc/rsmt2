//! A simple example
//!
//! This example uses the types defined in this module, they will systematically be imported in the
//! code samples.
//!
//!
//! We first need to define the expression type, and make it implement the
//! [`Expr2Smt`](crate::print::Expr2Smt) trait that writes it as an SMT-LIB 2 expression in a
//! writer.
//!
//! ## Print functions
//!
//! Since the structure for S-expressions is provided by users, they also need to provide functions
//! to print it in SMT Lib 2.
//!
//! To use all SMT Lib 2 commands in a type-safe manner, the library requires printers over
//!
//! - sorts: [`Sort2Smt`](crate::print::Sort2Smt) trait, *e.g.* for
//!   [`Solver::declare_fun`](crate::Solver::declare_fun),
//! - symbols: [`Sym2Smt`](crate::print::Sym2Smt) trait, *e.g.* for
//!   [`Solver::declare_fun`](crate::Solver::declare_fun),
//! - expressions: [`Expr2Smt`](crate::print::Expr2Smt) trait, *e.g.* for
//!   [`Solver::assert`](crate::Solver::assert).
//!
//! All user-provided printing functions take some *information*. That way, users can pass some
//! information to, say, `assert` that can modify printing. This is typically used when dealing with
//! transition systems to perform "print-time unrolling". See the
//! [`examples::print_time`](crate::examples::print_time) module if you're interested; the example
//! below will not use print-time information.
//!
//! ```rust
//! extern crate rsmt2;
//!
//! use rsmt2::print::Expr2Smt;
//! use rsmt2::SmtRes;
//! use rsmt2::examples::simple::{ Op, Cst };
//!
//! /// An example of expression.
//! pub enum Expr {
//!     /// A constant.
//!     C(Cst),
//!     /// Variable.
//!     V(String),
//!     /// Operator application.
//!     O( Op, Vec<Expr> ),
//! }
//! impl Expr {
//!     pub fn cst<C: Into<Cst>>(c: C) -> Self {
//!         Expr::C( c.into() )
//!     }
//! }
//! impl Expr2Smt<()> for Expr {
//!     fn expr_to_smt2<Writer>(
//!         & self, w: & mut Writer, _: ()
//!     ) -> SmtRes<()>
//!     where Writer: ::std::io::Write {
//!         let mut stack = vec![ (false, vec![self], false) ];
//!         while let Some((space, mut to_write, closing_paren)) = stack.pop() {
//!             if let Some(next) = to_write.pop() {
//!                 if space {
//!                     write!(w, " ") ?
//!                 }
//!                 // We have something to print, push the rest back.
//!                 stack.push((space, to_write, closing_paren));
//!                 match * next {
//!                     Expr::C(cst) => write!(w, "{}", cst) ?,
//!                     Expr::V(ref var) => write!(w, "{}", var) ?,
//!                     Expr::O(op, ref sub_terms) => {
//!                         write!(w, "({}", op) ?;
//!                         stack.push((true, sub_terms.iter().rev().collect(), true))
//!                     },
//!                 }
//!             } else {
//!                 // No more things to write at this level.
//!                 if closing_paren {
//!                     write!(w, ")") ?
//!                 }
//!             }
//!         }
//!         Ok(())
//!     }
//! }
//!
//! # fn main() {}
//! ```
//!
//! For convenience, all the `...2Smt` traits are implemented for `& str`. This is useful for
//! testing and maybe *very* simple application. Here, we won't implement
//! [`Sym2Smt`](crate::print::Sym2Smt) or [`Sort2Smt`](crate::print::Sort2Smt) and rely on `& str`
//! for symbols and sorts. Using a solver then boils down to creating a [`Solver`](crate::Solver)
//! which wraps a z3 process and provides most of the SMT-LIB 2.5 commands.
//!
//! ```rust
//! extern crate rsmt2;
//!
//! use rsmt2::Solver;
//! use rsmt2::examples::simple::{ Op, Cst, Expr };
//! # fn main() {
//!
//! let mut solver = Solver::default_z3(()).expect(
//!     "could not spawn solver kid"
//! );
//!
//! let v_1 = "v_1".to_string();
//! let v_2 = "v_2".to_string();
//!
//! solver.declare_const( & v_1, & "Bool" ).expect(
//!     "while declaring v_1"
//! );
//! solver.declare_const( & v_2, & "Int" ).expect(
//!     "while declaring v_2"
//! );
//!
//! let expr = Expr::O(
//!     Op::Disj, vec![
//!         Expr::O(
//!             Op::Ge, vec![ Expr::cst(-7), Expr::V( v_2.clone() ) ]
//!         ),
//!         Expr::V( v_1.clone() )
//!     ]
//! );
//!
//! solver.assert( & expr ).expect(
//!     "while asserting an expression"
//! );
//!
//! if solver.check_sat().expect("during check sat") {
//!     ()
//! } else {
//!     panic!("expected sat, got unsat")
//! }
//!
//! solver.kill().unwrap()
//! # }
//! ```
//!
//! Note the `unit` parameter that we passed to the `solver` function: `solver(& mut kid, ())`. This
//! is actually the parser the solver should use when it needs to parse values, symbols, types... In
//! the example above, we only asked for the satisfiability of the assertions. If we had asked for a
//! model, the compiler would have complained by saying that our parser `()` does not implement the
//! right parsing traits.
//!
//! ## The parser
//!
//! This example will only use [`Solver::get_model`](crate::Solver::get_model), which only requires
//! [`IdentParser`](crate::parse::IdentParser) and [`ModelParser`](crate::parse::ModelParser). In
//! most cases, an empty parser `struct` with the right implementations should be enough.
//!
//! ```rust
//! # #[macro_use]
//! # extern crate error_chain;
//! extern crate rsmt2;
//!
//! use rsmt2::SmtRes;
//! use rsmt2::parse::{ IdentParser, ModelParser };
//! use rsmt2::examples::simple::Cst;
//!
//! /// Empty parser structure, we will not maintain any context.
//! #[derive(Clone, Copy)]
//! pub struct Parser;
//! impl<'a> IdentParser<String, String, & 'a str> for Parser {
//!     fn parse_ident(self, input: & 'a str) -> SmtRes<String> {
//!         Ok( input.to_string() )
//!     }
//!     fn parse_type(self, input: & 'a str) -> SmtRes<String> {
//!         match input {
//!             "Int" => Ok( "Int".into() ),
//!             "Bool" => Ok( "Bool".into() ),
//!             sort => bail!("unexpected sort `{}`", sort),
//!         }
//!     }
//! }
//! impl<'a> ModelParser<String, String, Cst, & 'a str> for Parser {
//!     fn parse_value(
//!         self, input: & 'a str,
//!         _ident: & String, _signature: & [ (String, String) ], _type: & String,
//!     ) -> SmtRes<Cst> {
//!         match input.trim() {
//!             "true" => Ok( Cst::B(true) ),
//!             "false" => Ok( Cst::B(false) ),
//!             int => {
//!                 use std::str::FromStr;
//!                 let s = int.trim();
//!                 if let Ok(res) = isize::from_str(s) {
//!                     return Ok( Cst::I(res) )
//!                 } else if s.len() >= 4 {
//!                     if & s[0 .. 1] == "("
//!                     && & s[s.len() - 1 ..] == ")" {
//!                         let s = & s[1 .. s.len() - 1].trim();
//!                         if & s[0 .. 1] == "-" {
//!                             let s = & s[1..].trim();
//!                             if let Ok(res) = isize::from_str(s) {
//!                                 return Ok( Cst::I(- res) )
//!                             }
//!                         }
//!                     }
//!                 }
//!                 bail!("unexpected value `{}`", int)
//!             },
//!         }
//!     }
//! }
//! # fn main() {}
//! ```
//!
//! As a side note, it would have been simpler to implement
//! [`ModelParser`](crate::parse::ModelParser) with a [`& mut SmtParser`](crate::parse::SmtParser),
//! as it provides the parsers we needed.
//!
//! ```rust
//!
//! use rsmt2::SmtRes;
//! use rsmt2::parse::{ SmtParser, IdentParser, ModelParser };
//! use rsmt2::examples::simple::Cst;
//!
//!
//! #[derive(Clone, Copy)]
//! struct Parser;
//! impl<'a, Br> ModelParser<
//!     String, String, Cst, & 'a mut SmtParser<Br>
//! > for Parser
//! where Br: ::std::io::BufRead {
//!     fn parse_value(
//!         self, input: & 'a mut SmtParser<Br>,
//!         _ident: & String, _signature: & [ (String, String) ], _type: & String
//!     ) -> SmtRes<Cst> {
//!         use std::str::FromStr;
//!         if let Some(b) = input.try_bool() ? {
//!             Ok( Cst::B(b) )
//!         } else if let Some(int) = input.try_int(
//!             |int, pos| match isize::from_str(int) {
//!                 Ok(int) => if pos { Ok(int) } else { Ok(- int) },
//!                 Err(e) => Err(e),
//!             }
//!         ) ? {
//!             Ok( Cst::I(int) )
//!         } else {
//!             input.fail_with("unexpected value")
//!         }
//!     }
//! }
//! ```
//!
//! Anyway, once we pass `Parser` to the solver creation function, and all conditions are met to ask
//! the solver for a model.
//!
//! ```rust
//! # #[macro_use]
//! # extern crate error_chain;
//! extern crate rsmt2;
//!
//! use rsmt2::{ SmtRes, Solver };
//! use rsmt2::examples::simple::{
//!     Cst, Op, Expr, Parser
//! };
//!
//! # fn main() {
//!
//! let mut solver = Solver::default_z3(Parser).expect(
//!     "could not spawn solver kid"
//! );
//!
//! let v_1 = "v_1".to_string();
//! let v_2 = "v_2".to_string();
//!
//! solver.declare_const( & v_1, & "Bool" ).expect(
//!     "while declaring v_1"
//! );
//! solver.declare_const( & v_2, & "Int" ).expect(
//!     "while declaring v_2"
//! );
//!
//! let expr = Expr::O(
//!     Op::Disj, vec![
//!         Expr::O(
//!             Op::Ge, vec![ Expr::cst(-7), Expr::V( v_2.clone() ) ]
//!         ),
//!         Expr::V( v_1.clone() )
//!     ]
//! );
//!
//! solver.assert( & expr ).expect(
//!     "while asserting an expression"
//! );
//!
//! if solver.check_sat().expect("during check sat") {
//!
//!     let model = solver.get_model_const().expect(
//!         "while getting model"
//!     );
//!
//!     let mut okay = false;
//!     for (ident, typ, value) in model {
//!         if ident == v_1 {
//!             assert_eq!( typ, "Bool" );
//!             match value {
//!                 Cst::B(true) => okay = true,
//!                 Cst::B(false) => (),
//!                 Cst::I(int) => panic!(
//!                     "value for v_1 is `{}`, expected boolean", int
//!                 ),
//!             }
//!         } else if ident == v_2 {
//!             assert_eq!( typ, "Int" );
//!             match value {
//!                 Cst::I(i) if -7 >= i => okay = true,
//!                 Cst::I(_) => (),
//!                 Cst::B(b) => panic!(
//!                     "value for v_2 is `{}`, expected isize", b
//!                 ),
//!             }
//!         }
//!     }
//!
//!     if ! okay {
//!         panic!("got sat, but model is spurious")
//!     }
//!
//! } else {
//!     panic!("expected sat, got unsat")
//! }
//!
//! solver.kill().unwrap()
//! # }
//! ```

use crate::{
    errors::SmtRes,
    parse::{IdentParser, ModelParser},
    print::Expr2Smt,
};

#[cfg(test)]
use crate::examples::get_solver;

/// Operators. Just implements `Display`, never manipulated directly by the solver.
#[derive(Copy, Clone)]
pub enum Op {
    Add,
    Sub,
    Mul,
    Conj,
    Disj,
    Eql,
    Ge,
    Gt,
    Lt,
    Le,
}
impl ::std::fmt::Display for Op {
    fn fmt(&self, w: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        w.write_str(match *self {
            Op::Add => "+",
            Op::Sub => "-",
            Op::Mul => "*",
            Op::Conj => "and",
            Op::Disj => "or",
            Op::Eql => "=",
            Op::Ge => ">=",
            Op::Gt => ">",
            Op::Lt => "<",
            Op::Le => "<=",
        })
    }
}

/// A constant.
#[derive(Clone, Copy)]
pub enum Cst {
    /// Boolean constant.
    B(bool),
    /// Integer constant.
    I(isize),
}
impl ::std::fmt::Display for Cst {
    fn fmt(&self, w: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        match *self {
            Cst::B(b) => write!(w, "{}", b),
            Cst::I(i) if i >= 0 => write!(w, "{}", i),
            Cst::I(i) => write!(w, "(- {})", -i),
        }
    }
}
impl From<bool> for Cst {
    fn from(b: bool) -> Self {
        Cst::B(b)
    }
}
impl From<isize> for Cst {
    fn from(i: isize) -> Self {
        Cst::I(i)
    }
}

/// An example of expression.
pub enum Expr {
    /// A constant.
    C(Cst),
    /// Variable.
    V(String),
    /// Operator application.
    O(Op, Vec<Expr>),
}
impl Expr {
    pub fn cst<C: Into<Cst>>(c: C) -> Self {
        Expr::C(c.into())
    }
}
impl Expr2Smt<()> for Expr {
    fn expr_to_smt2<Writer>(&self, w: &mut Writer, _: ()) -> SmtRes<()>
    where
        Writer: ::std::io::Write,
    {
        let mut stack = vec![(false, vec![self], false)];
        while let Some((space, mut to_write, closing_paren)) = stack.pop() {
            if let Some(next) = to_write.pop() {
                if space {
                    write!(w, " ")?
                }
                // We have something to print, push the rest back.
                stack.push((space, to_write, closing_paren));
                match *next {
                    Expr::C(cst) => write!(w, "{}", cst)?,
                    Expr::V(ref var) => write!(w, "{}", var)?,
                    Expr::O(op, ref sub_terms) => {
                        write!(w, "({}", op)?;
                        stack.push((true, sub_terms.iter().rev().collect(), true))
                    }
                }
            } else if closing_paren {
                // No more things to write at this level.
                write!(w, ")")?
            }
        }
        Ok(())
    }
}

/// Empty parser structure, we will not maintain any context.
#[derive(Clone, Copy)]
pub struct Parser;
impl<'a> IdentParser<String, String, &'a str> for Parser {
    fn parse_ident(self, input: &'a str) -> SmtRes<String> {
        Ok(input.to_string())
    }
    fn parse_type(self, input: &'a str) -> SmtRes<String> {
        match input {
            "Int" => Ok("Int".into()),
            "Bool" => Ok("Bool".into()),
            sort => bail!("unexpected sort `{}`", sort),
        }
    }
}
impl<'a> ModelParser<String, String, Cst, &'a str> for Parser {
    fn parse_value(
        self,
        input: &'a str,
        _: &String,
        _: &[(String, String)],
        _: &String,
    ) -> SmtRes<Cst> {
        match input.trim() {
            "true" => Ok(Cst::B(true)),
            "false" => Ok(Cst::B(false)),
            int => {
                use std::str::FromStr;
                let s = int.trim();
                if let Ok(res) = isize::from_str(s) {
                    return Ok(Cst::I(res));
                } else if s.len() >= 4 && &s[0..1] == "(" && &s[s.len() - 1..] == ")" {
                    let s = &s[1..s.len() - 1].trim();
                    if &s[0..1] == "-" {
                        let s = &s[1..].trim();
                        if let Ok(res) = isize::from_str(s) {
                            return Ok(Cst::I(-res));
                        }
                    }
                }
                bail!("unexpected value `{}`", int)
            }
        }
    }
}

#[test]
fn run() {
    let mut solver = get_solver(Parser);

    let v_1 = "v_1".to_string();
    let v_2 = "v_2".to_string();

    solver
        .declare_const(&v_1, &"Bool")
        .expect("while declaring v_1");
    solver
        .declare_const(&v_2, &"Int")
        .expect("while declaring v_2");

    let expr = Expr::O(
        Op::Disj,
        vec![
            Expr::O(Op::Ge, vec![Expr::cst(-7), Expr::V(v_2.clone())]),
            Expr::V(v_1.clone()),
        ],
    );

    solver.assert(&expr).expect("while asserting an expression");

    if solver.check_sat().expect("during check sat") {
        let model = solver.get_model_const().expect("while getting model");

        let mut okay = false;
        for (ident, typ, value) in model {
            if ident == v_1 {
                assert_eq!(typ, "Bool");
                match value {
                    Cst::B(true) => okay = true,
                    Cst::B(false) => (),
                    Cst::I(int) => panic!("value for v_1 is `{}`, expected boolean", int),
                }
            } else if ident == v_2 {
                assert_eq!(typ, "Int");
                match value {
                    Cst::I(i) if -7 >= i => okay = true,
                    Cst::I(_) => (),
                    Cst::B(b) => panic!("value for v_2 is `{}`, expected isize", b),
                }
            }
        }

        if !okay {
            panic!("got sat, but model is spurious")
        }
    } else {
        panic!("expected sat, got unsat")
    }

    solver.kill().expect("killing solver")
}
