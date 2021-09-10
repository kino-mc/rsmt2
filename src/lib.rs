//! A wrapper around SMT Lib 2(.5)-compliant SMT solvers.
//!
//! See [`CHANGES.md`][changes] for the list of changes.
//!
//! If you use this library consider contacting us on the [repository][rsmt2] so that we can add
//! your project to the readme.
//!
//!
//!
//!
//! # Description
//!
//!
//! In rsmt2, solvers run in a separate process and communication is achieved *via* system pipes.
//! This means that to use a solver, it needs to be available as a binary in your path. For the
//! moment, only [z3] is officially supported, although there is experimental support for [cvc4] and
//! [yices 2].
//!
//! **NB**: most of the tests and documentation examples in this crate will not work unless you have
//! [z3] in your path under the name `z3`.
//!
//! This library does **not** have a structure for S-expressions. It must be provided by the user,
//! as well as the relevant printing and parsing functions. Printing-related traits are discussed in
//! the [`mod@print`] module, and parsing-related traits are in the [`mod@parse`] module.
//!
//!
//! # Note on Backend Solvers
//!
//! This crate supports the following solvers:
//!
//! - [z3]: full support
//! - [cvc4]: full support in theory, but only partially tested. Note that `get-value` is known to
//!   crash some versions of CVC4.
//! - [yices 2]: full support in theory, but only partially tested. Command `get-model` will only
//!   work on Yices 2 > `2.6.1`, and needs to be activated with [`SmtConf::models`]. To understand
//!   why, see <https://github.com/SRI-CSL/yices2/issues/162>.
//!
//! Since solver run as system processes on the end-user's system, it is hard to make any assumption
//! regarding the command that will run a particular solver. For this reason you should make sure
//! you allow your users to pass command that specifies how to run a given solver.You can take a
//! look at the [`custom_cmd` example] for guidance.
//!
//! Note that the command for each solver can be passed through environment variables, see
//! - the [`conf` module](self::conf) for general information,
//! - [`conf::Z3_ENV_VAR`],
//! - [`conf::CVC4_ENV_VAR`],
//! - [`conf::YICES_2_ENV_VAR`], and
//! - the [`conf::SmtConf::z3_or_env`], [`conf::SmtConf::cvc4_or_env`], and
//!   [`conf::SmtConf::yices_2_or_env`] constructors.
//!
//! # Very basic example
//!
//! String types already implement rsmt2's SMT-printing traits. It's not a scalable approach, but
//! it's useful for testing and explaining things. Let's create a solver first.
//!
//! This is typically done by creating an [`SmtConf`][SmtConf] solver configuration. This
//! configuration lets rsmt2 know which solver you plan on using, as well as override the command
//! used to launch it or activate model production.
//!
//! ```rust
//! let parser = ();
//! use rsmt2::SmtConf;
//!
//! let conf = SmtConf::default_z3();
//! let mut solver = conf.spawn(parser).unwrap();
//!
//! let is_sat = solver.check_sat().unwrap();
//! assert!(is_sat)
//! ```
//!
//! Notice that all three functions spawning a solver take a parser used to parse identifiers,
//! values and/or expressions. rsmt2 parses everything else (keywords and such), and lets users
//! handle the important parts. See the [`parse`](self::parse) module documentation for more
//! details.
//!
//! Our current parser `()` is enough for this example. We can even perform
//! [`check-sat`](Solver::check_sat)s since, unlike [`get-model`](Solver::get_model) for instance,
//! it does not require any user-data-structure-specific parsing. Let's declare a few symbols and
//! perform a check-sat.
//!
//! ```rust
//! # fn do_smt_stuff() -> ::rsmt2::SmtRes<()> {
//! use rsmt2::Solver;
//! let mut solver = Solver::default_z3(())?;
//!
//! solver.declare_const("n", "Int")?;
//! //     ^^^^^^^^^^^^^~~~ same as `declare-fun` for a nullary symbol
//! solver.declare_const("m", "Int")?;
//! solver.assert("(= (+ (* n n) (* m m)) 7)")?;
//!
//! let is_sat = solver.check_sat()?;
//! assert!(! is_sat);
//! # Ok(())
//! # }
//! # do_smt_stuff().unwrap()
//! ```
//!
//! We already knew there's no pair of integers the sum of the squares of which is equal to `7`, but
//! now we **proved** it.
//!
//!
//!
//!
//! # Parsing things
//!
//! If we want to be able to retrieve models, we need a parser that can parse two things:
//! identifiers, types and values. That is, we need a parser that implements
//! [`IdentParser`](parse::IdentParser) (identifiers and types) and
//! [`ModelParser`](parse::ModelParser) (values). The previous parser `()` doesn't, so calls to
//! [`Solver::get_model`] won't even compile.
//!
//! There's different ways to implement these traits, discussed in the [`parse`](self::parse) module
//! documentation. Let us be lazy and just have rsmt2 do the work for us. Note the (unnecessary) use
//! of [`Solver::define_fun`].
//!
//! ```rust
//! use rsmt2::{ Solver, SmtRes };
//! use rsmt2::parse::{ IdentParser, ModelParser };
//!
//! #[derive(Clone, Copy)]
//! struct Parser;
//!
//! impl<'a> IdentParser<String, String, & 'a str> for Parser {
//!     // Idents ~~~~~~~^^^^^^  ^^^^^^  ^^^^^^^^~~~~ Input
//!     //     Types ~~~~~~~~~~~~|
//!     fn parse_ident(self, input: & 'a str) -> SmtRes<String> {
//!         Ok(input.into())
//!     }
//!     fn parse_type(self, input: & 'a str) -> SmtRes<String> {
//!         Ok(input.into())
//!     }
//! }
//!
//! impl<'a> ModelParser<String, String, String, & 'a str> for Parser {
//!     // Idents ~~~~~~~^^^^^^  ^^^^^^  ^^^^^^  ^^^^^^^^~~~~ Input
//!     //         Types ~~~~~~~~|            |~~~~~ Values
//!     fn parse_value(
//!       self, input: & 'a str,
//!       ident: & String, params: & [ (String, String) ], typ: & String,
//!     ) -> SmtRes<String> {
//!       Ok(input.into())
//!     }
//! }
//!
//! # fn do_smt_stuff() -> ::rsmt2::SmtRes<()> {
//! let mut solver = Solver::default_z3(Parser)?;
//!
//! solver.define_fun(
//!          "sq", & [ ("n", "Int") ], "Int", "(* n n)"
//!     // fn sq        (n:   Int)  ->  Int   { n * n }
//! )?;
//! solver.declare_const("n", "Int")?;
//! solver.declare_const("m", "Int")?;
//!
//! solver.assert("(= (+ (sq n) (sq m)) 29)")?;
//! solver.assert("(and (< n 5) (> n 0) (> m 0))")?;
//!
//! let is_sat = solver.check_sat()?;
//! assert!(is_sat);
//! let mut model = solver.get_model()?;
//! model.sort(); // Order might vary, sorting for assert below.
//! assert_eq!(
//!     model,
//!     vec![
//!         ("m".into(), vec![], "Int".into(), "5".into()),
//!         ("n".into(), vec![], "Int".into(), "2".into()),
//!     ]
//! );
//! # Ok(())
//! # }
//! # do_smt_stuff().unwrap()
//! ```
//!
//!
//!
//!
//!
//! # Asynchronous check-sats.
//!
//! The check-sat command above is blocking, in that the caller cannot do anything until the backend
//! solver answers. Using the `print_check_sat...` and `parse_check_sat...` functions on [`Solver`],
//! users can issue the check-sat command, work on something else, and get the result later on.
//!
//! The `print_check_sat...` [`Solver`] functions return a
//! [`FutureCheckSat`](future::FutureCheckSat) required by the `parse_check_sat...` [`Solver`]
//! functions to guarantee statically that the parse request makes sense.
//! [`FutureCheckSat`](future::FutureCheckSat) is equivalent to unit and exists only at compile
//! time.
//!
//! Rewriting the previous example in an asynchronous fashion yields (omitting most of the
//! unmodified code):
//!
//! ```rust
//! # use rsmt2::{ Solver, SmtRes };
//! # use rsmt2::parse::{ IdentParser, ValueParser };
//! # #[derive(Clone, Copy)]
//! # struct Parser;
//! # impl<'a> IdentParser<String, String, & 'a str> for Parser {
//! #     fn parse_ident(self, input: & 'a str) -> SmtRes<String> {
//! #         Ok(input.into())
//! #     }
//! #     fn parse_type(self, input: & 'a str) -> SmtRes<String> {
//! #         Ok(input.into())
//! #     }
//! # }
//! # impl<'a> ValueParser<String, & 'a str> for Parser {
//! #     fn parse_value(self, input: & 'a str) -> SmtRes<String> {
//! #         Ok(input.into())
//! #     }
//! # }
//! # fn do_smt_stuff() -> ::rsmt2::SmtRes<()> {
//! # let mut solver = Solver::default_z3(Parser)?;
//! solver.define_fun(
//!     "sq", & [ ("n", "Int") ], "Int", "(* n n)"
//! )?;
//! solver.declare_const("n", "Int")?;
//! solver.declare_const("m", "Int")?;
//!
//! solver.assert("(= (+ (sq n) (sq m)) 29)")?;
//! solver.assert("(and (< n 5) (> n 0) (> m 0))")?;
//!
//! let my_check_sat = solver.print_check_sat()?;
//! // Solver is working, we can do other things.
//! let is_sat = solver.parse_check_sat(my_check_sat)?;
//! assert!(is_sat);
//! # Ok(())
//! # }
//! # do_smt_stuff().unwrap()
//! ```
//!
//!
//!
//! # Other SMT-LIB 2 commands
//!
//! Refer to [`Solver`]'s documentation for the complete list of SMT-LIB 2 commands.
//!
//!
//!
//!
//!
//!
//! # Activation literals
//!
//! Module [`actlit`](self::actlit) discusses rsmt2's API for *activation literals*, a alternative
//! to [`Solver::push`] and [`Solver::pop`] that's more limited but more efficient.
//!
//!
//!
//!
//!
//!
//!
//!
//!
//!
//! # Custom data structures
//!
//! Examples in the [`examples`](self::examples) module discusses in detail how to use rsmt2 with a
//! custom data structure. This includes implementing the [print traits](self::print) and writing a
//! more evolved parser. Examples are only visible if the `examples` features is active.
//!
//!
//!
//!
//!
//!
//!
//!
//! # Print-Time Information Passing
//!
//! The `print_time` example in [`examples`](self::examples) showcases print-time
//! information-passing. Proper documentation is somewhat lacking as it is a rather advanced topic,
//! and no one asked for more details about it.
//!
//! Print-time information is the reason for
//!
//! - the `Info` type parameter in the [`...2Smt` traits](self::print),
//! - all the `..._with` solver functions, such as [`Solver::assert_with`].
//!
//! Users can call these functions to pass information down to their own printers as commands are
//! written on the solver's input. The typical use-case is *print-time unrolling* when working with
//! transition systems. Given a transition relation `T` over a current and next state `s[0]` and
//! `s[1]`, *unrolling* consists in creating a sequence of states `s[0]`, `s[1]`, `s[2]`, ... such
//! that `T(s[0], s[1]) and T(s[1], s[2]) and ...`. Such a sequence is called a *trace*.
//!
//! Say the state `s` is some variables `(x, y)` and the transition relation is `T(s[0], s[1]) =
//! (x[1] == x[0] + 1) && (y[1] == 2 * y[0])`. Then in SMT-LIB, unrolling `T` twice looks like
//!
//! ```lisp
//! (define-fun trans ( (x_0 Int) (y_0 Int) (x_1 Int) (y_1 Int) ) Bool
//!     (and (= x_1 (+ x_0 1)) (= y_1 (* 2 y_0)) )
//! )
//!
//! (declare-fun x_0 () Int)
//! (declare-fun y_0 () Int)
//!
//! (declare-fun x_1 () Int)
//! (declare-fun y_1 () Int)
//!
//! (assert (trans x_0 y_0 x_1 y_1))
//!
//! (declare-fun x_2 () Int)
//! (declare-fun y_2 () Int)
//!
//! (assert (trans x_1 y_1 x_2 y_2))
//! ```
//!
//! In a model-checker, at each point of the unrolling one wants to (conditionally) assert terms
//! about a state, or a pair of succeeding states, but never more. Also, the "same" term will
//! typically be asserted for many different states / pair of states.
//!
//! Notice that if we want to assert `P(s) = x > 0` for `s[0]` and `s[1]`, then in theory we have to
//! create two terms `x_0 > 0` and `x_1 > 0`. By extension, these are called *unrollings* of `P`.
//! Now, these terms can end up being pretty big, and memory can become a problem, even with
//! [hashconsing][hashconsing].
//!
//! Creating a different term for each unrolling of `P`, asserting it, and then (usually) discarding
//! them right away is not practical time- and memory-wise. It is better if the term structure has a
//! notion of "current `x`" (`x_0`) and "next `x`" (`x_1`), and to decide how to print them *at
//! print-time* by passing an *offset* that's essentially an integer. It represents the offset for
//! the "current" state.
//!
//! So, from the term `x_1 > x_0` for instance, passing an offset of `3` to the printer would cause
//! `x_0` to be printed as `x_3` and `x_1` as `x_4`. Without creating anything, just from the
//! original term.
//!
//! This is the workflow showcased (but only partially explained) by `print_time` in
//! [`examples`](self::examples).
//!
//!
//!
//! # Asynchronous check-sat-s
//!
//! See the [`asynch` module](self::asynch) and [`Solver::async_check_sat_or_unk`].
//!
//!
//! [rsmt2]: https://github.com/kino-mc/rsmt2 (rsmt2 github repository)
//! [z3]: https://github.com/Z3Prover/z3 (z3 github repository)
//! [cvc4]: https://cvc4.github.io/ (cvc4 github pages)
//! [yices 2]: https://yices.csl.sri.com/ (yices 2 official page)
//! [changes]: https://github.com/kino-mc/rsmt2/blob/master/CHANGES.md (List of changes on github)
//! [hashconsing]: https://crates.io/crates/hashconsing (hashconsing crate on crates.io)
//! [`custom_cmd` example]: https://github.com/kino-mc/rsmt2/tree/master/examples/custom_cmd.rs
//! (Example of passing a custom solver command to rsmt2)

#![deny(missing_docs, rustdoc::broken_intra_doc_links)]

#[macro_use]
extern crate error_chain;

/// Common rsmt2 type and helpers.
pub mod prelude {
    pub use crate::{actlit, errors::SmtRes, parse::*, print::*, Logic, SmtConf, Solver};
}

/// Errors.
///
/// Aggregates I/O errors and rsmt2 specific errors.
pub mod errors {
    error_chain! {
        types {
            Error, ErrorKind, ResExt, SmtRes;
        }

        foreign_links {
            Io(::std::io::Error) #[doc = "IO error."];
        }

        errors {
            #[doc = "The solver reported `unknown`."]
            Unknown {
                description("smt solver reported `unknown`")
            }
            #[doc = "The solver reported `timeout`."]
            Timeout {
                description("smt solver reported `timeout`")
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

    impl ErrorKind {
        /// True if the error is `Unknown`.
        pub fn is_unknown(&self) -> bool {
            if let ErrorKind::Unknown = *self {
                true
            } else {
                false
            }
        }

        /// True if the error is `Timeout`.
        pub fn is_timeout(&self) -> bool {
            if let ErrorKind::Timeout = *self {
                true
            } else {
                false
            }
        }
    }

    impl Error {
        /// Multi-line, pretty representation of a chain of errors.
        pub fn to_ml_string(&self) -> String {
            let mut s = String::new();
            let mut pref = "";
            for e in self.iter() {
                let e_str = e.to_string();
                let lines = e_str.lines();
                let mut sub_pref = "- ";
                for line in lines {
                    s.push_str(pref);
                    s.push_str(sub_pref);
                    s.push_str(line);
                    pref = "\n";
                    sub_pref = "  ";
                }
            }
            s
        }
    }
}

#[macro_use]
mod common;

pub mod actlit;
pub mod asynch;
pub mod conf;
pub mod parse;
pub mod print;
mod solver;

pub use crate::common::Logic;
pub use crate::conf::{SmtConf, SmtStyle};
pub use crate::errors::SmtRes;
pub use crate::solver::Solver;

/// Promises for future results on ongoing computations.
pub mod future {
    pub use crate::solver::FutureCheckSat;
}

#[cfg(any(test, feature = "examples"))]
pub mod examples;

/// Examples, only available if the `examples` feature is active.
#[cfg(not(any(test, feature = "examples")))]
pub mod examples {}

#[cfg(test)]
mod tests;
