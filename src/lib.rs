// See the LICENSE files at the top-level directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![doc = r#"A wrapper around an SMT Lib 2(.5)-compliant SMT solver.

See [`CHANGES.md`](https://github.com/kino-mc/rsmt2/blob/master/README.md) for
the list of changes.

Solvers run in a separate process and communication is achieved *via* system
pipes.

This library does **not** have a structure for S-expressions. It should be
provided by the user, as well as the relevant printing and parsing functions.

If you use this library consider contacting us on the [repository](https://github.com/kino-mc/rsmt2) so that we can add your project to the readme.

## `async` versus `sync`

The functions corresponding to SMT Lib 2 queries come in two flavors,
asynchronous and synchronous.

*Synchronous* means that the query is printed on the solver's stdin, and the
result is parsed **right away**. Users get control back whenever the solver is
done working and parsing is done.
In other words, synchronous queries are *blocking*.

*Asynchronous* means that after the query is printed and control is given back
to the user. To retrieve the result, users must call the relevant `parse_...`
function. For instance, `parse_sat` for `check_sat`.
In other words, asynchronous queries are *non-blocking*. Not that `parse_...`
functions **are** blocking though.


The example below uses synchronous queries.


## Workflow

The worflow is introduced below on a running example. It uses a structure for
S-expressions representing the unrolling of some predicates over discrete
time-steps.

**N.B.** this example is very naïve and should not be used as is.

S-expressions are defined as follows:

```
/// Under the hood a symbol is a string.
type Sym = String ;

/// A variable wraps a symbol.
#[derive(Debug,Clone,PartialEq)]
enum Var {
  /// Variable constant in time (Non-Stateful Var: SVar).
  NSVar(Sym),
  /// State variable in the current step.
  SVar0(Sym),
  /// State variable in the next step.
  SVar1(Sym),
}

/// A constant.
#[derive(Debug,Clone,PartialEq)]
enum Const {
  /// Boolean constant.
  BConst(bool),
  /// Integer constant.
  IConst(usize),
  /// Rational constant.
  RConst(usize,usize),
}

/// An S-expression.
#[derive(Debug,Clone,PartialEq)]
enum SExpr {
  /// A variable.
  Id(Var),
  /// A constant.
  Val(Const),
  /// An application of function symbol.
  App(Sym, Vec<SExpr>),
}
```

We then use `Offset` to specify what the index of the current and next step
are:

```
# /// Under the hood a symbol is a string.
# type Sym = String ;
# 
# /// A variable wraps a symbol.
# #[derive(Debug,Clone,PartialEq)]
# enum Var {
#   /// Variable constant in time (Non-Stateful Var: SVar).
#   NSVar(Sym),
#   /// State variable in the current step.
#   SVar0(Sym),
#   /// State variable in the next step.
#   SVar1(Sym),
# }
# 
# /// A constant.
# #[derive(Debug,Clone,PartialEq)]
# enum Const {
#   /// Boolean constant.
#   BConst(bool),
#   /// Integer constant.
#   IConst(usize),
#   /// Rational constant.
#   RConst(usize,usize),
# }
# 
# /// An S-expression.
# #[derive(Debug,Clone,PartialEq)]
# enum SExpr {
#   /// A variable.
#   Id(Var),
#   /// A constant.
#   Val(Const),
#   /// An application of function symbol.
#   App(Sym, Vec<SExpr>),
# }
#
/// An offset gives the index of current and next step.
#[derive(Debug,Clone,Copy,PartialEq)]
struct Offset(usize, usize) ;

/// A symbol is a variable and an offset.
#[derive(Debug,Clone,PartialEq)]
struct Symbol<'a, 'b>(& 'a Var, & 'b Offset) ;

/// An unrolled SExpr.
#[derive(Debug,Clone,PartialEq)]
struct Unrolled<'a, 'b>(& 'a SExpr, & 'b Offset) ;
```

### Print functions

Since the structure for S-expressions is provided by the users, they also need
to provide functions to print it in SMT Lib 2.

To use all SMT Lib 2 commands in a type-safe manner, the library requires
printers over

* sorts: `Sort2Smt` trait (*e.g.* for `declare-fun`),
* symbols: `Sym2Smt` trait (*e.g.* for `declare-fun`),
* expressions: `Expr2Smt` trait (*e.g.* for `assert`).

The last two are parameterized by a Type for the information at print time.
Commands using the user's structure for printing are enriched with a field
to pass information down to the printer.

For convenience, all these traits are implemented for `& str`. This is useful
for testing and maybe *very* simple application.

In our example, printing a symbol / an expression requires an offset. The idea
is that `Symbol` (`Unrolled`) will implement `Sym2Smt` (`Expr2Smt`). For sorts
we will use `& str` for simplicity.

We begin by writing printing functions taking an offset for our structure, as
well as simple helper funtions:

```
extern crate rsmt2 ;

use std::io::Write ;

use rsmt2::* ;
use rsmt2::errors::* ;

use Var::* ;
use Const::* ;
use SExpr::* ;

# /// Under the hood a symbol is a string.
# type Sym = String ;
# 
# /// A variable wraps a symbol.
# #[derive(Debug,Clone,PartialEq)]
# enum Var {
#   /// Variable constant in time (Non-Stateful Var: SVar).
#   NSVar(Sym),
#   /// State variable in the current step.
#   SVar0(Sym),
#   /// State variable in the next step.
#   SVar1(Sym),
# }
# 
# /// A constant.
# #[derive(Debug,Clone,PartialEq)]
# enum Const {
#   /// Boolean constant.
#   BConst(bool),
#   /// Integer constant.
#   IConst(usize),
#   /// Rational constant.
#   RConst(usize,usize),
# }
# 
# /// An S-expression.
# #[derive(Debug,Clone,PartialEq)]
# enum SExpr {
#   /// A variable.
#   Id(Var),
#   /// A constant.
#   Val(Const),
#   /// An application of function symbol.
#   App(Sym, Vec<SExpr>),
# }
#
# /// An offset gives the index of current and next step.
# #[derive(Debug,Clone,Copy,PartialEq)]
# struct Offset(usize, usize) ;
# 
# /// A symbol is a variable and an offset.
# #[derive(Debug,Clone,PartialEq)]
# struct Symbol<'a, 'b>(& 'a Var, & 'b Offset) ;
# 
# /// An unrolled SExpr.
# #[derive(Debug,Clone,PartialEq)]
# struct Unrolled<'a, 'b>(& 'a SExpr, & 'b Offset) ;
#
impl Var {
  pub fn nsvar(s: & str) -> Self { NSVar(s.to_string()) }
  pub fn svar0(s: & str) -> Self { SVar0(s.to_string()) }
  pub fn svar1(s: & str) -> Self { SVar1(s.to_string()) }
  /// Given an offset, a variable can be printed in SMT Lib 2.
  #[inline(always)]
  pub fn to_smt2<Writer: Write>(
    & self, writer: & mut Writer, off: & Offset
  ) -> Res<()> {
    match * self {
      NSVar(ref sym) => write!(writer, "|{}|", sym) ?,
      /// SVar at 0, we use the index of the current step.
      SVar0(ref sym) => write!(writer, "|{}@{}|", sym, off.0) ?,
      /// SVar at 1, we use the index of the next step.
      SVar1(ref sym) => write!(writer, "|{}@{}|", sym, off.1) ?,
    }
    Ok(())
  }
  /// Given an offset, a variable can become a Symbol.
  pub fn to_sym<'a, 'b>(& 'a self, off: & 'b Offset) -> Symbol<'a, 'b> {
    Symbol(self, off)
  }
}

impl Const {
  /// A constant can be printed in SMT Lib 2.
  #[inline(always)]
  pub fn to_smt2<Writer: Write>(& self, writer: & mut Writer) -> Res<()> {
    match * self {
      BConst(ref b) => write!(writer, "{}", b) ?,
      IConst(ref i) => write!(writer, "{}", i) ?,
      RConst(ref num, ref den) => write!(writer, "(/ {} {})", num, den) ?,
    }
    Ok(())
  }
}

impl SExpr {
  pub fn app(sym: & str, args: Vec<SExpr>) -> Self {
    App(sym.to_string(), args)
  }
  /// Given an offset, an S-expression can be printed in SMT Lib 2.
  pub fn to_smt2<Writer: Write>(
    & self, writer: & mut Writer, off: & Offset
  ) -> Res<()> {
    match * self {
      Id(ref var) => var.to_smt2(writer, off),
      Val(ref cst) => cst.to_smt2(writer),
      App(ref sym, ref args) => {
        write!(writer, "({}", sym) ? ;
        for ref arg in args {
          write!(writer, " ") ? ;
          arg.to_smt2(writer, off) ?
        }
        write!(writer, ")") ? ;
        Ok(())
      }
    }
  }
  /// Given an offset, an S-expression can be unrolled.
  pub fn unroll<'a, 'b>(& 'a self, off: & 'b Offset) -> Unrolled<'a,'b> {
    Unrolled(self, off)
  }
}
# fn main() {}
```

It is now easy to implement `Sym2Smt` and `Expr2Smt`:

```
#
# extern crate rsmt2 ;
# 
# use std::io::Write ;
# 
# use rsmt2::* ;
# use rsmt2::errors::* ;
# 
# use Var::* ;
# use Const::* ;
# use SExpr::* ;
# 
# /// Under the hood a symbol is a string.
# type Sym = String ;
# 
# /// A variable wraps a symbol.
# #[derive(Debug,Clone,PartialEq)]
# enum Var {
#   /// Variable constant in time (Non-Stateful Var: SVar).
#   NSVar(Sym),
#   /// State variable in the current step.
#   SVar0(Sym),
#   /// State variable in the next step.
#   SVar1(Sym),
# }
# 
# /// A constant.
# #[derive(Debug,Clone,PartialEq)]
# enum Const {
#   /// Boolean constant.
#   BConst(bool),
#   /// Integer constant.
#   IConst(usize),
#   /// Rational constant.
#   RConst(usize,usize),
# }
# 
# /// An S-expression.
# #[derive(Debug,Clone,PartialEq)]
# enum SExpr {
#   /// A variable.
#   Id(Var),
#   /// A constant.
#   Val(Const),
#   /// An application of function symbol.
#   App(Sym, Vec<SExpr>),
# }
#
# /// An offset gives the index of current and next step.
# #[derive(Debug,Clone,Copy,PartialEq)]
# struct Offset(usize, usize) ;
# 
# /// A symbol is a variable and an offset.
# #[derive(Debug,Clone,PartialEq)]
# struct Symbol<'a, 'b>(& 'a Var, & 'b Offset) ;
# 
# /// An unrolled SExpr.
# #[derive(Debug,Clone,PartialEq)]
# struct Unrolled<'a, 'b>(& 'a SExpr, & 'b Offset) ;
#
# impl Var {
#   pub fn nsvar(s: & str) -> Self { NSVar(s.to_string()) }
#   pub fn svar0(s: & str) -> Self { SVar0(s.to_string()) }
#   pub fn svar1(s: & str) -> Self { SVar1(s.to_string()) }
#   /// Given an offset, a variable can be printed in SMT Lib 2.
#   #[inline(always)]
#   pub fn to_smt2<Writer: Write>(
#     & self, writer: & mut Writer, off: & Offset
#   ) -> Res<()> {
#     match * self {
#       NSVar(ref sym) => write!(writer, "|{}|", sym) ?,
#       /// SVar at 0, we use the index of the current step.
#       SVar0(ref sym) => write!(writer, "|{}@{}|", sym, off.0) ?,
#       /// SVar at 1, we use the index of the next step.
#       SVar1(ref sym) => write!(writer, "|{}@{}|", sym, off.1) ?,
#     }
#     Ok(())
#   }
#   /// Given an offset, a variable can become a Symbol.
#   pub fn to_sym<'a, 'b>(& 'a self, off: & 'b Offset) -> Symbol<'a, 'b> {
#     Symbol(self, off)
#   }
# }
# 
# impl Const {
#   /// A constant can be printed in SMT Lib 2.
#   #[inline(always)]
#   pub fn to_smt2<Writer: Write>(& self, writer: & mut Writer) -> Res<()> {
#     match * self {
#       BConst(ref b) => write!(writer, "{}", b) ?,
#       IConst(ref i) => write!(writer, "{}", i) ?,
#       RConst(ref num, ref den) => write!(writer, "(/ {} {})", num, den) ?,
#     }
#     Ok(())
#   }
# }
# 
# impl SExpr {
#   pub fn app(sym: & str, args: Vec<SExpr>) -> Self {
#     App(sym.to_string(), args)
#   }
#   /// Given an offset, an S-expression can be printed in SMT Lib 2.
#   pub fn to_smt2<Writer: Write>(
#     & self, writer: & mut Writer, off: & Offset
#   ) -> Res<()> {
#     match * self {
#       Id(ref var) => var.to_smt2(writer, off),
#       Val(ref cst) => cst.to_smt2(writer),
#       App(ref sym, ref args) => {
#         write!(writer, "({}", sym) ? ;
#         for ref arg in args {
#           write!(writer, " ") ? ;
#           arg.to_smt2(writer, off) ?
#         }
#         write!(writer, ")") ? ;
#         Ok(())
#       }
#     }
#   }
#   /// Given an offset, an S-expression can be unrolled.
#   pub fn unroll<'a, 'b>(& 'a self, off: & 'b Offset) -> Unrolled<'a,'b> {
#     Unrolled(self, off)
#   }
# }
/// A symbol can be printed in SMT Lib 2.
impl<'a, 'b> Sym2Smt<()> for Symbol<'a,'b> {
  fn sym_to_smt2<Writer: Write>(
    & self, writer: & mut Writer, _: & ()
  ) -> Res<()> {
    self.0.to_smt2(writer, self.1)
  }
}

/// An unrolled SExpr can be printed in SMT Lib 2.
impl<'a, 'b> Expr2Smt<()> for Unrolled<'a,'b> {
  fn expr_to_smt2<Writer: Write>(
    & self, writer: & mut Writer, _: & ()
  ) -> Res<()> {
    self.0.to_smt2(writer, self.1)
  }
}
# fn main() {}
```


### Before writing the parsers...

...we can actually already test our structure. To create a solver, one must
give an implementation of `ParseSmt2`. But we can define a dummy parser as long
as we don't actually need to parse anything specific to our structure.

That is, as long as we only use the `check-sat` and `check-sat-assuming`
queries. On the other hand, we will not be able to call, say, `get-model` for
now because then we would need to provide a parser for symbols and values.

So, we define a dummy parser for now and perform a `check-sat`:

```
// Parser library.
#[macro_use]
extern crate nom ;
extern crate rsmt2 ;

use nom::IResult ;

# use std::io::Write ;
# 
# use rsmt2::* ;
# use rsmt2::errors::* ;
# 
# use Var::* ;
# use Const::* ;
# use SExpr::* ;
# 
# /// Under the hood a symbol is a string.
# type Sym = String ;
# 
# /// A variable wraps a symbol.
# #[derive(Debug,Clone,PartialEq)]
# enum Var {
#   /// Variable constant in time (Non-Stateful Var: SVar).
#   NSVar(Sym),
#   /// State variable in the current step.
#   SVar0(Sym),
#   /// State variable in the next step.
#   SVar1(Sym),
# }
# 
# /// A constant.
# #[derive(Debug,Clone,PartialEq)]
# enum Const {
#   /// Boolean constant.
#   BConst(bool),
#   /// Integer constant.
#   IConst(usize),
#   /// Rational constant.
#   RConst(usize,usize),
# }
# 
# /// An S-expression.
# #[derive(Debug,Clone,PartialEq)]
# enum SExpr {
#   /// A variable.
#   Id(Var),
#   /// A constant.
#   Val(Const),
#   /// An application of function symbol.
#   App(Sym, Vec<SExpr>),
# }
#
# /// An offset gives the index of current and next step.
# #[derive(Debug,Clone,Copy,PartialEq)]
# struct Offset(usize, usize) ;
# 
# /// A symbol is a variable and an offset.
# #[derive(Debug,Clone,PartialEq)]
# struct Symbol<'a, 'b>(& 'a Var, & 'b Offset) ;
# 
# /// An unrolled SExpr.
# #[derive(Debug,Clone,PartialEq)]
# struct Unrolled<'a, 'b>(& 'a SExpr, & 'b Offset) ;
#
# impl Var {
#   pub fn nsvar(s: & str) -> Self { NSVar(s.to_string()) }
#   pub fn svar0(s: & str) -> Self { SVar0(s.to_string()) }
#   pub fn svar1(s: & str) -> Self { SVar1(s.to_string()) }
#   /// Given an offset, a variable can be printed in SMT Lib 2.
#   #[inline(always)]
#   pub fn to_smt2<Writer: Write>(
#     & self, writer: & mut Writer, off: & Offset
#   ) -> Res<()> {
#     match * self {
#       NSVar(ref sym) => write!(writer, "|{}|", sym) ?,
#       /// SVar at 0, we use the index of the current step.
#       SVar0(ref sym) => write!(writer, "|{}@{}|", sym, off.0) ?,
#       /// SVar at 1, we use the index of the next step.
#       SVar1(ref sym) => write!(writer, "|{}@{}|", sym, off.1) ?,
#     }
#     Ok(())
#   }
#   /// Given an offset, a variable can become a Symbol.
#   pub fn to_sym<'a, 'b>(& 'a self, off: & 'b Offset) -> Symbol<'a, 'b> {
#     Symbol(self, off)
#   }
# }
# 
# impl Const {
#   /// A constant can be printed in SMT Lib 2.
#   #[inline(always)]
#   pub fn to_smt2<Writer: Write>(
#     & self, writer: & mut Writer
#   ) -> Res<()> {
#     match * self {
#       BConst(ref b) => write!(writer, "{}", b) ?,
#       IConst(ref i) => write!(writer, "{}", i) ?,
#       RConst(ref num, ref den) => write!(writer, "(/ {} {})", num, den) ?,
#     }
#     Ok(())
#   }
# }
# 
# impl SExpr {
#   pub fn app(sym: & str, args: Vec<SExpr>) -> Self {
#     App(sym.to_string(), args)
#   }
#   /// Given an offset, an S-expression can be printed in SMT Lib 2.
#   pub fn to_smt2<Writer: Write>(
#     & self, writer: & mut Writer, off: & Offset
#   ) -> Res<()> {
#     match * self {
#       Id(ref var) => var.to_smt2(writer, off),
#       Val(ref cst) => cst.to_smt2(writer),
#       App(ref sym, ref args) => {
#         write!(writer, "({}", sym) ? ;
#         for ref arg in args {
#           write!(writer, " ") ? ;
#           arg.to_smt2(writer, off) ?
#         }
#         write!(writer, ")") ? ;
#         Ok(())
#       }
#     }
#   }
#   /// Given an offset, an S-expression can be unrolled.
#   pub fn unroll<'a, 'b>(& 'a self, off: & 'b Offset) -> Unrolled<'a,'b> {
#     Unrolled(self, off)
#   }
# }
# /// A symbol can be printed in SMT Lib 2.
# impl<'a, 'b> Sym2Smt<()> for Symbol<'a,'b> {
#   fn sym_to_smt2<Writer: Write>(
#     & self, writer: & mut Writer, _: & ()
#   ) -> Res<()> {
#     self.0.to_smt2(writer, self.1)
#   }
# }
# 
# /// An unrolled SExpr can be printed in SMT Lib 2.
# impl<'a, 'b> Expr2Smt<()> for Unrolled<'a,'b> {
#   fn expr_to_smt2<Writer: Write>(
#     & self, writer: & mut Writer, _: & ()
#   ) -> Res<()> {
#     self.0.to_smt2(writer, self.1)
#   }
# }
/// Dummy parser.
struct Parser ;
impl ParseSmt2 for Parser {
  type Ident = Var ;
  type Value = Const ;
  type Expr = SExpr ;
  type Proof = () ;
  type I = () ;

  fn parse_ident<'a>(
    & self, array: & 'a [u8]
  ) -> IResult<& 'a [u8], Var> {
    panic!("not implemented")
  }
  fn parse_value<'a>(
    & self, array: & 'a [u8]
  ) -> IResult<& 'a [u8], Const> {
    panic!("not implemented")
  }
  fn parse_expr<'a>(
    & self, array: & 'a [u8], _: & ()
  ) -> IResult<& 'a [u8], SExpr> {
    panic!("not implemented")
  }
  fn parse_proof<'a>(
    & self, _: & 'a [u8]
  ) -> IResult<& 'a [u8], ()> {
    panic!("not implemented")
  }
}

/// Convenience macro.
macro_rules! smtry {
  ($e:expr, failwith $( $msg:expr ),+) => (
    match $e {
      Ok(something) => something,
      Err(e) => panic!( $($msg),+ , e)
    }
  ) ;
}


fn main() {
  use rsmt2::* ;

  let conf = SolverConf::z3() ;

  let mut kid = match Kid::new(conf) {
    Ok(kid) => kid,
    Err(e) => panic!("Could not spawn solver kid: {:?}", e)
  } ;

  {

    let mut solver = smtry!(
      solver(& mut kid, Parser),
      failwith "could not create solver: {:?}"
    ) ;

    let nsv = Var::nsvar("non stateful var") ;
    let s_nsv = Id(nsv.clone()) ;
    let sv_0 = Var::svar0("stateful var") ;
    let s_sv_0 = Id(sv_0.clone()) ;
    let app2 = SExpr::app("not", vec![ s_sv_0.clone() ]) ;
    let app1 = SExpr::app("and", vec![ s_nsv.clone(), app2.clone() ]) ;
    let offset1 = Offset(0,1) ;

    let sym = nsv.to_sym(& offset1) ;
    smtry!(
      solver.declare_fun(& sym, &[] as & [& str], & "bool", & ()),
      failwith "declaration failed: {:?}"
    ) ;

    let sym = sv_0.to_sym(& offset1) ;
    smtry!(
      solver.declare_fun(& sym, &[] as & [& str], & "bool", & ()),
      failwith "declaration failed: {:?}"
    ) ;

    let expr = app1.unroll(& offset1) ;
    smtry!(
      solver.assert(& expr, & ()),
      failwith "assert failed: {:?}"
    ) ;

    match smtry!(
      solver.check_sat(),
      failwith "error in checksat: {:?}"
    ) {
      true => (),
      false => panic!("expected sat, got unsat"),
    }

  }

  smtry!(
    kid.kill(),
    failwith "error while killing solver: {:?}"
  ) ;
}
```

### Parsing

This library uses the [`nom`][nom page] parser combinator library. Users can
use whatever they want as long as they implement the `ParseSmt2` trait.

Note that there is no reason *a priori* for the structures returned by the
parsers to be the same as the one used for printing. In our running example,
parsing a variable with an offset of `6` (in a `get-values` for example) as
an `SExpr` is ambiguous. Is `6` the index of the current or next step? What's
the other index?

For this simple example however, we will use the same structures. Despite the
fact that it makes little sense.

Unfortunately writing the code as a (**tested**) documentation comment does not
work currently. The `nom` macros recurse quite deeply and the thread for the
test overflows its stack. I do not know how to fix this. Please contact me if
you do.

The implementation of the parser, as well as an example using `get-model` and
`get-values` are written as a private test/example directly in the source. You
can view it [here][full example].


[nom page]: https://crates.io/crates/nom (crates.io pafe of the nom library)
[full example]: ../src/rsmt2/src/example.rs.html (Full example)
"#]

#[macro_use]
extern crate error_chain ;
#[macro_use]
extern crate nom ;

/// Errors of this library.
pub mod errors {
  error_chain!{
    types {
      Error, ErrorKind, ResExt, Res ;
    }

    foreign_links {
      Io(::std::io::Error) #[doc = "IO error."] ;
    }

    errors {
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

      #[doc = "Parsing error ([`nom`](https://crates.io/crates/nom) style)."]
      ParseError(e: ::nom::IError) {
        description("parsing error")
        display("parsing error: \"{:?}\"", e)
      }
    }
  }
}

#[macro_use]
mod common ;
mod conf ;
mod parse ;
mod solver ;

mod example ;

pub use common::* ;
pub use conf::* ;
pub use solver::{
  solver,
  Kid, Solver, PlainSolver, TeeSolver,
  Query, QueryExpr, QueryExprInfo, QueryIdent,
} ;

/// Internal traits used to build solvers.
pub mod internals {
  pub use solver::{ SolverBasic, SolverPrims } ;
}