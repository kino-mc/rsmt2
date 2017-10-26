#![doc = r#"A wrapper around an SMT Lib 2(.5)-compliant SMT solver.

See [`CHANGES.md`](https://github.com/kino-mc/rsmt2/blob/master/README.md) for
the list of changes.

Solvers run in a separate process and communication is achieved *via* system
pipes.

This library does **not** have a structure for S-expressions. It should be
provided by the user, as well as the relevant printing and parsing functions.

If you use this library consider contacting us on the
[repository](https://github.com/kino-mc/rsmt2) so that we can add your project
to the readme.

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

/// A type.
#[derive(Debug,Clone,Copy,PartialEq)]
enum Type { Int, Bool, Real }

/// A constant.
#[derive(Debug,Clone,PartialEq)]
enum Const {
  /// Boolean constant.
  BConst(bool),
  /// Integer constant.
  IConst(isize),
  /// Rational constant.
  RConst(isize,usize),
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
# /// A type.
# #[derive(Debug,Clone,Copy,PartialEq)]
# enum Type { Int, Bool, Real }
# 
# /// A constant.
# #[derive(Debug,Clone,PartialEq)]
# enum Const {
#   /// Boolean constant.
#   BConst(bool),
#   /// Integer constant.
#   IConst(isize),
#   /// Rational constant.
#   RConst(isize,usize),
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
use rsmt2::parse::* ;
use rsmt2::SmtRes ;

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
# /// A type.
# #[derive(Debug,Clone,Copy,PartialEq)]
# enum Type { Int, Bool, Real }
# 
# /// A constant.
# #[derive(Debug,Clone,PartialEq)]
# enum Const {
#   /// Boolean constant.
#   BConst(bool),
#   /// Integer constant.
#   IConst(isize),
#   /// Rational constant.
#   RConst(isize,usize),
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
  pub fn to_smt2<Writer: Write>(
    & self, writer: & mut Writer, off: & Offset
  ) -> SmtRes<()> {
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
  pub fn to_smt2<Writer: Write>(& self, writer: & mut Writer) -> SmtRes<()> {
    match * self {
      BConst(b) => write!(writer, "{}", b) ?,
      IConst(i) => {
        let neg = i < 0 ;
        if neg { write!(writer, "(- ") ? }
        write!(writer, "{}", i.abs()) ? ;
        if neg { write!(writer, ")") ? }
      },
      RConst(num, den) => {
        let neg = num < 0 ;
        if neg { write!(writer, "(- ") ? }
        write!(writer, "(/ {} {})", num, den) ? ;
        if neg { write!(writer, ")") ? }
      },
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
  ) -> SmtRes<()> {
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
# use rsmt2::parse::* ;
# use rsmt2::SmtRes ;
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
# /// A type.
# #[derive(Debug,Clone,Copy,PartialEq)]
# enum Type { Int, Bool, Real }
# 
# /// A constant.
# #[derive(Debug,Clone,PartialEq)]
# enum Const {
#   /// Boolean constant.
#   BConst(bool),
#   /// Integer constant.
#   IConst(isize),
#   /// Rational constant.
#   RConst(isize,usize),
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
#   ) -> SmtRes<()> {
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
#   pub fn to_smt2<Writer: Write>(& self, writer: & mut Writer) -> SmtRes<()> {
#     match * self {
#       BConst(b) => write!(writer, "{}", b) ?,
#       IConst(i) => {
#         let neg = i < 0 ;
#         if neg { write!(writer, "(- ") ? }
#         write!(writer, "{}", i.abs()) ? ;
#         if neg { write!(writer, ")") ? }
#       },
#       RConst(num, den) => {
#         let neg = num < 0 ;
#         if neg { write!(writer, "(- ") ? }
#         write!(writer, "(/ {} {})", num, den) ? ;
#         if neg { write!(writer, ")") ? }
#       },
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
#   ) -> SmtRes<()> {
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
use rsmt2::to_smt::{ Sym2Smt, Expr2Smt } ;

/// A symbol can be printed in SMT Lib 2.
impl<'a, 'b> Sym2Smt<()> for Symbol<'a,'b> {
  fn sym_to_smt2<Writer: Write>(
    & self, writer: & mut Writer, _: ()
  ) -> SmtRes<()> {
    self.0.to_smt2(writer, self.1)
  }
}

/// An unrolled SExpr can be printed in SMT Lib 2.
impl<'a, 'b> Expr2Smt<()> for Unrolled<'a,'b> {
  fn expr_to_smt2<Writer: Write>(
    & self, writer: & mut Writer, _: ()
  ) -> SmtRes<()> {
    self.0.to_smt2(writer, self.1)
  }
}
# fn main() {}
```


### Before writing the parsers...

...we can actually already test our structure. To create a solver, one must
provide a parser for the custom structures. It will be used by some of the
functions in the [`Solver`](./trait.Solver.html) trait. The
[`get_model`](trait.Solver.html#method.get_model) function for instance
requires the parser to implement the [IdentParser](trait.IdentParser.html) and
[ValueParser](trait.ValueParser.html) traits.

Most of the other functions of `Solver` do not require anything however, this
the case of [`check_sat`](trait.Solver.html#method.check_sat) for example.

```
# // Parser library.
# extern crate rsmt2 ;
# use std::io::Write ;
# 
# use rsmt2::* ;
# use rsmt2::parse::* ;
# use rsmt2::SmtRes ;
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
# /// A type.
# #[derive(Debug,Clone,Copy,PartialEq)]
# enum Type { Int, Bool, Real }
# 
# /// A constant.
# #[derive(Debug,Clone,PartialEq)]
# enum Const {
#   /// Boolean constant.
#   BConst(bool),
#   /// Integer constant.
#   IConst(isize),
#   /// Rational constant.
#   RConst(isize,usize),
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
#   ) -> SmtRes<()> {
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
#   ) -> SmtRes<()> {
#     match * self {
#       BConst(b) => write!(writer, "{}", b) ?,
#       IConst(i) => {
#         let neg = i < 0 ;
#         if neg { write!(writer, "(- ") ? }
#         write!(writer, "{}", i.abs()) ? ;
#         if neg { write!(writer, ")") ? }
#       },
#       RConst(num, den) => {
#         let neg = num < 0 ;
#         if neg { write!(writer, "(- ") ? }
#         write!(writer, "(/ {} {})", num, den) ? ;
#         if neg { write!(writer, ")") ? }
#       },
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
#   ) -> SmtRes<()> {
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
# use rsmt2::to_smt::* ;
# /// A symbol can be printed in SMT Lib 2.
# impl<'a, 'b> Sym2Smt<()> for Symbol<'a,'b> {
#   fn sym_to_smt2<Writer: Write>(
#     & self, writer: & mut Writer, _: ()
#   ) -> SmtRes<()> {
#     self.0.to_smt2(writer, self.1)
#   }
# }
# 
# /// An unrolled SExpr can be printed in SMT Lib 2.
# impl<'a, 'b> Expr2Smt<()> for Unrolled<'a,'b> {
#   fn expr_to_smt2<Writer: Write>(
#     & self, writer: & mut Writer, _: ()
#   ) -> SmtRes<()> {
#     self.0.to_smt2(writer, self.1)
#   }
# }
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
  use rsmt2::conf::SolverConf ;

  let conf = SolverConf::z3() ;

  let mut kid = match Kid::new(conf) {
    Ok(kid) => kid,
    Err(e) => panic!("Could not spawn solver kid: {:?}", e)
  } ;

  {

    let mut solver = smtry!(
      solver(& mut kid, ()),
      failwith "could not create solver: {:?}"
    ) ;

    let nsv = Var::nsvar("non-stateful var") ;
    let s_nsv = Id(nsv.clone()) ;
    let sv_0 = Var::svar0("stateful var") ;
    let s_sv_0 = Id(sv_0.clone()) ;
    let app2 = SExpr::app("not", vec![ s_sv_0.clone() ]) ;
    let app1 = SExpr::app("and", vec![ s_nsv.clone(), app2.clone() ]) ;
    let offset1 = Offset(0,1) ;

    let sym = nsv.to_sym(& offset1) ;
    smtry!(
      solver.declare_fun(& sym, &[] as & [& str], & "Bool", ()),
      failwith "declaration failed: {:?}"
    ) ;

    let sym = sv_0.to_sym(& offset1) ;
    smtry!(
      solver.declare_fun(& sym, &[] as & [& str], & "Bool", ()),
      failwith "declaration failed: {:?}"
    ) ;

    let expr = app1.unroll(& offset1) ;
    smtry!(
      solver.assert(& expr, ()),
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

Below is the end of our running example. The `*Parser` traits are discussed in
the [`parse`][parse] module.

Note that there is no reason *a priori* for the structures returned by the
parsers to be the same as the one used for printing. In this example our state
variables have a notion of offset. It is retrieved during parsing, that's why
our `IdentParser` returns `(Var, Option<usize>)`.

```
# // Parser library.
# extern crate rsmt2 ;
# use std::io::Write ;
# 
# use rsmt2::* ;
# use rsmt2::parse::* ;
# use rsmt2::SmtRes ;
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
# impl Var {
#   fn sym(& self) -> & str {
#     match * self { NSVar(ref s) => s, SVar0(ref s) => s, SVar1(ref s) => s }
#   }
# }
#
# /// A type.
# #[derive(Debug,Clone,Copy,PartialEq)]
# enum Type { Int, Bool, Real }
# 
# /// A constant.
# #[derive(Debug,Clone,PartialEq)]
# enum Const {
#   /// Boolean constant.
#   BConst(bool),
#   /// Integer constant.
#   IConst(isize),
#   /// Rational constant.
#   RConst(isize,usize),
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
#   ) -> SmtRes<()> {
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
#   ) -> SmtRes<()> {
#     match * self {
#       BConst(b) => write!(writer, "{}", b) ?,
#       IConst(i) => {
#         let neg = i < 0 ;
#         if neg { write!(writer, "(- ") ? }
#         write!(writer, "{}", i.abs()) ? ;
#         if neg { write!(writer, ")") ? }
#       },
#       RConst(num, den) => {
#         let neg = num < 0 ;
#         if neg { write!(writer, "(- ") ? }
#         write!(writer, "(/ {} {})", num, den) ? ;
#         if neg { write!(writer, ")") ? }
#       },
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
#   ) -> SmtRes<()> {
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
# use rsmt2::to_smt::* ;
# /// A symbol can be printed in SMT Lib 2.
# impl<'a, 'b> Sym2Smt<()> for Symbol<'a,'b> {
#   fn sym_to_smt2<Writer: Write>(
#     & self, writer: & mut Writer, _: ()
#   ) -> SmtRes<()> {
#     self.0.to_smt2(writer, self.1)
#   }
# }
# 
# /// An unrolled SExpr can be printed in SMT Lib 2.
# impl<'a, 'b> Expr2Smt<()> for Unrolled<'a,'b> {
#   fn expr_to_smt2<Writer: Write>(
#     & self, writer: & mut Writer, _: ()
#   ) -> SmtRes<()> {
#     self.0.to_smt2(writer, self.1)
#   }
# }
# /// Convenience macro.
# macro_rules! smtry {
#   ($e:expr, failwith $( $msg:expr ),+) => (
#     match $e {
#       Ok(something) => something,
#       Err(e) => panic!( $($msg),+ , e)
#     }
#   ) ;
# }
#[macro_use]
extern crate error_chain ;

/// Parser structure.
#[derive(Clone, Copy)]
struct Parser ;
impl<'a> IdentParser< 'a, (Var, Option<usize>), Type, & 'a str > for Parser {
  fn parse_ident(self, s: & 'a str) -> SmtRes<(Var, Option<usize>)> {
    if s.len() <= 2 { bail!("not one of my idents...") }
    let s = & s[ 1 .. (s.len() - 1) ] ; // Removing surrounding pipes.
    let mut parts = s.split("@") ;
    let id = if let Some(id) = parts.next() { id.to_string() } else {
      bail!("nothing between my pipes!")
    } ;
    if let Some(index) = parts.next() {
      use std::str::FromStr ;
      Ok( (
        Var::SVar0(id),
        match usize::from_str(index) {
          Ok(index) => Some(index),
          Err(e) => bail!("while parsing the offset in `{}`: {}", s, e)
        }
      ) )
    } else {
      Ok( (Var::NSVar(id), None) )
    }
  }
  fn parse_type(self, s: & 'a str) -> SmtRes<Type> {
    match s {
      "Int" => Ok( Type::Int ),
      "Bool" => Ok( Type::Bool ),
      "Real" => Ok( Type::Real ),
      _ => bail!( format!("unknown type `{}`", s) ),
    }
  }
}

impl<'a> ValueParser< 'a, Const, & 'a str > for Parser {
  fn parse_value(self, s: & 'a str) -> SmtRes<Const> {
    if s == "true" {
      return Ok( Const::BConst(true) )
    } else if s == "false" {
      return Ok( Const::BConst(false) )
    }

    use std::str::FromStr ;
    if let Ok(int) = isize::from_str(s) {
      return Ok( Const::IConst(int) )
    }

    let msg = format!("unexpected value `{}`", s) ;

    let mut tokens = s.split_whitespace() ;

    match tokens.next() {
      Some("(/") => (),
      Some("(") => if tokens.next() != Some("/") { bail!(msg) },
      _ => bail!(msg),
    }

    match (
      tokens.next().map(|t| isize::from_str(t)),
      tokens.next().map(|t| usize::from_str(t)),
      tokens.next(),
    ) {
      (
        Some(Ok(num)), Some(Ok(den)), Some(")")
      ) => Ok( Const::RConst(num, den) ),
      _ => bail!(msg),
    }
  }
}

fn main() {
  use rsmt2::* ;
  use rsmt2::conf::SolverConf ;

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

    let nsv = Var::nsvar("non-stateful var") ;
    let s_nsv = Id(nsv.clone()) ;
    let sv_0 = Var::svar0("stateful var") ;
    let s_sv_0 = Id(sv_0.clone()) ;
    let app2 = SExpr::app("not", vec![ s_sv_0.clone() ]) ;
    let app1 = SExpr::app("and", vec![ s_nsv.clone(), app2.clone() ]) ;
    let offset1 = Offset(0,1) ;

    let sym = nsv.to_sym(& offset1) ;
    smtry!(
      solver.declare_fun(& sym, &[] as & [& str], & "Bool", ()),
      failwith "declaration failed: {:?}"
    ) ;

    let sym = sv_0.to_sym(& offset1) ;
    smtry!(
      solver.declare_fun(& sym, &[] as & [& str], & "Bool", ()),
      failwith "declaration failed: {:?}"
    ) ;

    let expr = app1.unroll(& offset1) ;
    smtry!(
      solver.assert(& expr, ()),
      failwith "assert failed: {:?}"
    ) ;

    if ! smtry!(
      solver.check_sat(),
      failwith "error in checksat: {:?}"
    ) {
      panic!("expected sat, got unsat")
    }

    let model = smtry!(
      solver.get_model(),
      failwith "while getting model: {:?}"
    ) ;

    for ((var, off), args, typ, val) in model {
      if var.sym() == "stateful var" {
        assert_eq!(off, Some(0)) ;
        assert_eq!(typ, Type::Bool) ;
        assert_eq!(val, Const::BConst(false))
      } else if var.sym() == "non-stateful var" {
        assert_eq!(off, None) ;
        assert_eq!(typ, Type::Bool) ;
        assert_eq!(val, Const::BConst(true))
      }
    }
  }

  smtry!(
    kid.kill(),
    failwith "error while killing solver: {:?}"
  ) ;
}
```

Note that it would have been a bit easier to implement `ValueParser` with a [`&
mut SmtParser`][smt parser], as it provides the parsers we want.

```
# // Parser library.
# extern crate rsmt2 ;
# use std::io::Write ;
# 
# use rsmt2::* ;
# use rsmt2::parse::* ;
# use rsmt2::SmtRes ;
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
# impl Var {
#   fn sym(& self) -> & str {
#     match * self { NSVar(ref s) => s, SVar0(ref s) => s, SVar1(ref s) => s }
#   }
# }
#
# /// A type.
# #[derive(Debug,Clone,Copy,PartialEq)]
# enum Type { Int, Bool, Real }
# 
# /// A constant.
# #[derive(Debug,Clone,PartialEq)]
# enum Const {
#   /// Boolean constant.
#   BConst(bool),
#   /// Integer constant.
#   IConst(isize),
#   /// Rational constant.
#   RConst(isize,usize),
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
#   ) -> SmtRes<()> {
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
#   ) -> SmtRes<()> {
#     match * self {
#       BConst(b) => write!(writer, "{}", b) ?,
#       IConst(i) => {
#         let neg = i < 0 ;
#         if neg { write!(writer, "(- ") ? }
#         write!(writer, "{}", i.abs()) ? ;
#         if neg { write!(writer, ")") ? }
#       },
#       RConst(num, den) => {
#         let neg = num < 0 ;
#         if neg { write!(writer, "(- ") ? }
#         write!(writer, "(/ {} {})", num, den) ? ;
#         if neg { write!(writer, ")") ? }
#       },
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
#   ) -> SmtRes<()> {
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
# use rsmt2::to_smt::* ;
# /// A symbol can be printed in SMT Lib 2.
# impl<'a, 'b> Sym2Smt<()> for Symbol<'a,'b> {
#   fn sym_to_smt2<Writer: Write>(
#     & self, writer: & mut Writer, _: ()
#   ) -> SmtRes<()> {
#     self.0.to_smt2(writer, self.1)
#   }
# }
# 
# /// An unrolled SExpr can be printed in SMT Lib 2.
# impl<'a, 'b> Expr2Smt<()> for Unrolled<'a,'b> {
#   fn expr_to_smt2<Writer: Write>(
#     & self, writer: & mut Writer, _: ()
#   ) -> SmtRes<()> {
#     self.0.to_smt2(writer, self.1)
#   }
# }
# /// Convenience macro.
# macro_rules! smtry {
#   ($e:expr, failwith $( $msg:expr ),+) => (
#     match $e {
#       Ok(something) => something,
#       Err(e) => panic!( $($msg),+ , e)
#     }
#   ) ;
# }
# #[macro_use]
# extern crate error_chain ;
# 
# /// Parser structure.
# #[derive(Clone, Copy)]
# struct Parser ;
# impl<'a> IdentParser< 'a, (Var, Option<usize>), Type, & 'a str > for Parser {
#   fn parse_ident(self, s: & 'a str) -> SmtRes<(Var, Option<usize>)> {
#     if s.len() <= 2 { bail!("not one of my idents...") }
#     let s = & s[ 1 .. (s.len() - 1) ] ; // Removing surrounding pipes.
#     let mut parts = s.split("@") ;
#     let id = if let Some(id) = parts.next() { id.to_string() } else {
#       bail!("nothing between my pipes!")
#     } ;
#     if let Some(index) = parts.next() {
#       use std::str::FromStr ;
#       Ok( (
#         Var::SVar0(id),
#         match usize::from_str(index) {
#           Ok(index) => Some(index),
#           Err(e) => bail!("while parsing the offset in `{}`: {}", s, e)
#         }
#       ) )
#     } else {
#       Ok( (Var::NSVar(id), None) )
#     }
#   }
#   fn parse_type(self, s: & 'a str) -> SmtRes<Type> {
#     match s {
#       "Int" => Ok( Type::Int ),
#       "Bool" => Ok( Type::Bool ),
#       "Real" => Ok( Type::Real ),
#       _ => bail!( format!("unknown type `{}`", s) ),
#     }
#   }
# }

use rsmt2::parse::SmtParser ;

impl<'a, Br> ValueParser< 'a, Const, & 'a mut SmtParser<Br> > for Parser
where Br: ::std::io::BufRead {
  fn parse_value(self, input: & 'a mut SmtParser<Br>) -> SmtRes<Const> {
    use std::str::FromStr ;
    if let Some(b) = input.try_bool() ? {
      Ok( Const::BConst(b) )
    } else if let Some(int) = input.try_int(
      |int, pos| match isize::from_str(int) {
        Ok(int) => if pos { Ok(int) } else { Ok(- int) },
        Err(e) => Err(e),
      }
    ) ? {
      Ok( Const::IConst(int) )
    } else if let Some((num, den)) = input.try_rat (
      |num, den, pos| match (isize::from_str(num), usize::from_str(den)) {
        (Ok(num), Ok(den)) => if pos {
          Ok((num, den))
        } else { Ok((- num, den)) },
        (Err(e), _) | (_, Err(e)) => Err( format!("{}", e) )
      }
    ) ? {
      Ok( Const::RConst(num, den) )
    } else {
      input.fail_with("unexpected value")
    }
  }
}

# fn main() {
#   use rsmt2::* ;
#   use rsmt2::conf::SolverConf ;
# 
#   let conf = SolverConf::z3() ;
# 
#   let mut kid = match Kid::new(conf) {
#     Ok(kid) => kid,
#     Err(e) => panic!("Could not spawn solver kid: {:?}", e)
#   } ;
# 
#   {
# 
#     let mut solver = smtry!(
#       solver(& mut kid, Parser),
#       failwith "could not create solver: {:?}"
#     ) ;
# 
#     let nsv = Var::nsvar("non-stateful var") ;
#     let s_nsv = Id(nsv.clone()) ;
#     let sv_0 = Var::svar0("stateful var") ;
#     let s_sv_0 = Id(sv_0.clone()) ;
#     let app2 = SExpr::app("not", vec![ s_sv_0.clone() ]) ;
#     let app1 = SExpr::app("and", vec![ s_nsv.clone(), app2.clone() ]) ;
#     let offset1 = Offset(0,1) ;
# 
#     let sym = nsv.to_sym(& offset1) ;
#     smtry!(
#       solver.declare_fun(& sym, &[] as & [& str], & "Bool", ()),
#       failwith "declaration failed: {:?}"
#     ) ;
# 
#     let sym = sv_0.to_sym(& offset1) ;
#     smtry!(
#       solver.declare_fun(& sym, &[] as & [& str], & "Bool", ()),
#       failwith "declaration failed: {:?}"
#     ) ;
# 
#     let expr = app1.unroll(& offset1) ;
#     smtry!(
#       solver.assert(& expr, ()),
#       failwith "assert failed: {:?}"
#     ) ;
# 
#     if ! smtry!(
#       solver.check_sat(),
#       failwith "error in checksat: {:?}"
#     ) {
#       panic!("expected sat, got unsat")
#     }
# 
#     let model = smtry!(
#       solver.get_model(),
#       failwith "while getting model: {:?}"
#     ) ;
# 
#     for ((var, off), args, typ, val) in model {
#       if var.sym() == "stateful var" {
#         assert_eq!(off, Some(0)) ;
#         assert_eq!(typ, Type::Bool) ;
#         assert_eq!(val, Const::BConst(false))
#       } else if var.sym() == "non-stateful var" {
#         assert_eq!(off, None) ;
#         assert_eq!(typ, Type::Bool) ;
#         assert_eq!(val, Const::BConst(true))
#       }
#     }
#   }
# 
#   smtry!(
#     kid.kill(),
#     failwith "error while killing solver: {:?}"
#   ) ;
# }
```

[parse]: parse/index.html (parse module)
[smt parser]: parse/struct.SmtParser.html (SmtParser structure)
"#]

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
pub use solver::{
  solver, Kid, Solver, PlainSolver, TeeSolver
} ;

// /// Internal traits used to build solvers.
// pub mod internals {
//   pub use parse::SmtParser ;
//   pub use solver::SolverBasic ;
// }

/// Traits your types must implement so that `rsmt2` can use them.
pub mod to_smt {
  pub use common::{ Expr2Smt, Sort2Smt, Sym2Smt } ;
}





#[cfg(test)]
mod top {

  // Parser library.
  use std::io::Write ;
  
  use * ;
  use parse::* ;
  
  use self::Var::* ;
  use self::Const::* ;
  use self::SExpr::* ;
  
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
  impl Var {
    fn sym(& self) -> & str {
      match * self { NSVar(ref s) => s, SVar0(ref s) => s, SVar1(ref s) => s }
    }
  }

  /// A type.
  #[derive(Debug,Clone,Copy,PartialEq)]
  enum Type { Int, Bool, Real }
  
  /// A constant.
  #[derive(Debug,Clone,PartialEq)]
  enum Const {
    /// Boolean constant.
    BConst(bool),
    /// Integer constant.
    IConst(isize),
    /// Rational constant.
    RConst(isize,usize),
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

  /// An offset gives the index of current and next step.
  #[derive(Debug,Clone,Copy,PartialEq)]
  struct Offset(usize, usize) ;
  
  /// A symbol is a variable and an offset.
  #[derive(Debug,Clone,PartialEq)]
  struct Symbol<'a, 'b>(& 'a Var, & 'b Offset) ;
  
  /// An unrolled SExpr.
  #[derive(Debug,Clone,PartialEq)]
  struct Unrolled<'a, 'b>(& 'a SExpr, & 'b Offset) ;

  impl Var {
    pub fn nsvar(s: & str) -> Self { NSVar(s.to_string()) }
    pub fn svar0(s: & str) -> Self { SVar0(s.to_string()) }
    pub fn svar1(s: & str) -> Self { SVar1(s.to_string()) }
    /// Given an offset, a variable can be printed in SMT Lib 2.
    #[inline(always)]
    pub fn to_smt2<Writer: Write>(
      & self, writer: & mut Writer, off: & Offset
    ) -> SmtRes<()> {
      match * self {
        NSVar(ref sym) => write!(writer, "|{}|", sym) ?,
        // SVar at 0, we use the index of the current step.
        SVar0(ref sym) => write!(writer, "|{}@{}|", sym, off.0) ?,
        // SVar at 1, we use the index of the next step.
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
    pub fn to_smt2<Writer: Write>(
      & self, writer: & mut Writer
    ) -> SmtRes<()> {
      match * self {
        BConst(b) => write!(writer, "{}", b) ?,
        IConst(i) => {
          let neg = i < 0 ;
          if neg { write!(writer, "(- ") ? }
          write!(writer, "{}", i.abs()) ? ;
          if neg { write!(writer, ")") ? }
        },
        RConst(num, den) => {
          let neg = num < 0 ;
          if neg { write!(writer, "(- ") ? }
          write!(writer, "(/ {} {})", num, den) ? ;
          if neg { write!(writer, ")") ? }
        },
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
    ) -> SmtRes<()> {
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
  use to_smt::* ;
  /// A symbol can be printed in SMT Lib 2.
  impl<'a, 'b> Sym2Smt<()> for Symbol<'a,'b> {
    fn sym_to_smt2<Writer: Write>(
      & self, writer: & mut Writer, _: ()
    ) -> SmtRes<()> {
      self.0.to_smt2(writer, self.1)
    }
  }
  
  /// An unrolled SExpr can be printed in SMT Lib 2.
  impl<'a, 'b> Expr2Smt<()> for Unrolled<'a,'b> {
    fn expr_to_smt2<Writer: Write>(
      & self, writer: & mut Writer, _: ()
    ) -> SmtRes<()> {
      self.0.to_smt2(writer, self.1)
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
  
  /// Parser structure.
  #[derive(Clone, Copy)]
  struct Parser ;
  impl<'a> IdentParser< 'a, (Var, Option<usize>), Type, & 'a str > for Parser {
    fn parse_ident(self, s: & 'a str) -> SmtRes<(Var, Option<usize>)> {
      if s.len() <= 2 { bail!("not one of my idents...") }
      let s = & s[ 1 .. (s.len() - 1) ] ; // Removing surrounding pipes.
      let mut parts = s.split("@") ;
      let id = if let Some(id) = parts.next() { id.to_string() } else {
        bail!("nothing between my pipes!")
      } ;
      if let Some(index) = parts.next() {
        use std::str::FromStr ;
        Ok( (
          Var::SVar0(id),
          match usize::from_str(index) {
            Ok(index) => Some(index),
            Err(e) => bail!("while parsing the offset in `{}`: {}", s, e)
          }
        ) )
      } else {
        Ok( (Var::NSVar(id), None) )
      }
    }
    fn parse_type(self, s: & 'a str) -> SmtRes<Type> {
      match s {
        "Int" => Ok( Type::Int ),
        "Bool" => Ok( Type::Bool ),
        "Real" => Ok( Type::Real ),
        _ => bail!( format!("unknown type `{}`", s) ),
      }
    }
  }

  use parse::SmtParser ;

  impl<'a, Br> ValueParser< 'a, Const, & 'a mut SmtParser<Br> > for Parser
  where Br: ::std::io::BufRead {
    fn parse_value(self, input: & 'a mut SmtParser<Br>) -> SmtRes<Const> {
      use std::str::FromStr ;
      if let Some(b) = input.try_bool() ? {
        Ok( Const::BConst(b) )
      } else if let Some(int) = input.try_int(
        |int, pos| match isize::from_str(int) {
          Ok(int) => if pos { Ok(int) } else { Ok(- int) },
          Err(e) => Err(e),
        }
      ) ? {
        Ok( Const::IConst(int) )
      } else if let Some((num, den)) = input.try_rat (
        |num, den, pos| match (isize::from_str(num), usize::from_str(den)) {
          (Ok(num), Ok(den)) => if pos {
            Ok((num, den))
          } else { Ok((- num, den)) },
          (Err(e), _) | (_, Err(e)) => Err( format!("{}", e) )
        }
      ) ? {
        Ok( Const::RConst(num, den) )
      } else {
        input.fail_with("unexpected value")
      }
    }
  }

  #[test]
  fn declare_non_nullary_fun() {
    use * ;
    use conf::SolverConf ;
  
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

      smtry!(
        solver.declare_fun(
          "my_fun", & [ "Int", "Real", "Bool" ], "Real", ()
        ), failwith "during function declaration: {:?}"
      )
    }
  }

  #[test]
  fn complete_1() {
    use * ;
    use conf::SolverConf ;
  
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
  
      let nsv_0 = Var::nsvar("non-stateful var") ;
      let s_nsv_0 = Id(nsv_0.clone()) ;
      let nsv_1 = Var::nsvar("also non-stateful") ;
      let s_nsv_1 = Id(nsv_1.clone()) ;
      let sv_0 = Var::svar0("stateful var") ;
      let s_sv_0 = Id(sv_0.clone()) ;
      let sv_1 = Var::svar1("also stateful") ;
      let s_sv_1 = Id(sv_1.clone()) ;
      let app1 = SExpr::app("not", vec![ s_sv_0.clone() ]) ;
      let app2 = SExpr::app(
        ">", vec![ s_sv_1.clone(), Val( Const::IConst(7) ) ]
      ) ;
      let app3 = SExpr::app(
        "=", vec![
          Val( Const::RConst(- 7, 3) ),
          SExpr::app("+", vec![ s_nsv_1.clone(), Val(Const::RConst(2, 1)) ])
        ]
      ) ;
      let app = SExpr::app("and", vec![ s_nsv_0.clone(), app1, app2, app3 ]) ;
      let offset1 = Offset(0,1) ;
  
      let sym = nsv_0.to_sym(& offset1) ;
      smtry!(
        solver.declare_const(& sym, & "Bool", ()),
        failwith "declaration failed: {:?}"
      ) ;
  
      let sym = nsv_1.to_sym(& offset1) ;
      smtry!(
        solver.declare_const(& sym, & "Real", ()),
        failwith "declaration failed: {:?}"
      ) ;
  
      let sym = sv_0.to_sym(& offset1) ;
      smtry!(
        solver.declare_const(& sym, & "Bool", ()),
        failwith "declaration failed: {:?}"
      ) ;
  
      let sym = sv_1.to_sym(& offset1) ;
      smtry!(
        solver.declare_const(& sym, & "Int", ()),
        failwith "declaration failed: {:?}"
      ) ;
  
      let expr = app.unroll(& offset1) ;
      smtry!(
        solver.assert(& expr, ()),
        failwith "assert failed: {:?}"
      ) ;
  
      assert!(
        smtry!(
          solver.check_sat(),
          failwith "error in checksat: {:?}"
        )
      ) ;
  
      let model = smtry!(
        solver.get_model(),
        failwith "while getting model: {:?}"
      ) ;
  
      for ((var, off), _, typ, val) in model {
        if var.sym() == "stateful var" {
          assert_eq!(off, Some(0)) ;
          assert_eq!(typ, Type::Bool) ;
          assert_eq!(val, Const::BConst(false))
        } else if var.sym() == "also stateful" {
          assert_eq!(off, Some(1)) ;
          assert_eq!(typ, Type::Int) ;
          if let Const::IConst(val) = val {
            assert!( val > 7 )
          } else {
            panic!("expected variable, got {:?}", val)
          }
        } else if var.sym() == "non-stateful var" {
          assert_eq!(off, None) ;
          assert_eq!(typ, Type::Bool) ;
          assert_eq!(val, Const::BConst(true))
        } else if var.sym() == "also non-stateful" {
          assert_eq!(off, None) ;
          assert_eq!(typ, Type::Real) ;
          if let Const::RConst(num, den) = val {
            assert_eq!( num * 3 + (2 * 3 * den as isize), (7 * den as isize) )
          } else {
            panic!("expected variable, got {:?}", val)
          }
        }
      }
    }
  
    kid.kill().expect("kill") ;
  }
}