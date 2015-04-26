#![ doc = "
Drivers for the different solvers.
"]

use std::io::{Read, Write} ;

use ::common::* ;
use ::solver_traits::* ;

pub trait GenericPrinter<
  Ident: Printable,
  Sort: Printable,
  Expr: Printable,
> : Writable {

  #[inline]
  fn check_sat_assuming_command(& self) -> & 'static str ;

  fn comment(& mut self, lines: ::std::str::Lines) -> IoResUnit {
    for line in lines { try!( write!(self.writer(), ";; {}\n", line) ) } ;
    write!(self.writer(), "\n")
  }

  // |===| (Re)starting and terminating.

  fn reset(& mut self) -> IoResUnit {
    write!(self.writer(), "(reset)\n\n")
  }
  fn set_logic(& mut self, logic: & Logic) -> IoResUnit {
    try!( write!(self.writer(), "(set-logic ") ) ;
    try!( logic.to_smt2(self.writer()) ) ;
    write!(self.writer(), ")\n\n")
  }
  fn set_option(& mut self, option: & str, value: & str) -> IoResUnit {
    write!(self.writer(), "(set-option {} {})\n\n", option, value)
  }
  fn exit(& mut self) -> IoResUnit {
    write!(self.writer(), "(exit)\n")
  }

  // |===| Modifying the assertion stack.

  fn push(& mut self, n: & u8) -> IoResUnit {
    write!(self.writer(), "(push {})\n\n", n)
  }
  fn pop(& mut self, n: & u8) -> IoResUnit {
    write!(self.writer(), "(pop {})\n\n", n)
  }
  fn reset_assertions(& mut self) -> IoResUnit {
    write!(self.writer(), "(reset-assertions)\n\n")
  }

  // |===| Introducing new symbols.

  fn declare_sort(& mut self, sort: Sort, arity: & u8) -> IoResUnit {
    try!( write!(self.writer(), "(declare-sort ") ) ;
    try!( sort.to_smt2(self.writer()) ) ;
    write!(self.writer(), " {})\n\n", arity)
  }
  fn define_sort(
    & mut self, sort: Sort, args: & [ Expr ], body: Expr
  ) -> IoResUnit {
    try!( write!(self.writer(), "( define-sort\n   ( ") ) ;
    for arg in args {
      try!( arg.to_smt2(self.writer()) ) ;
      try!( write!(self.writer(), " ") )
    } ;
    try!( write!(self.writer(), ")\n   ") ) ;
    try!( body.to_smt2(self.writer()) ) ;
    write!(self.writer(), "\n)\n\n")
  }
  fn declare_fun(
    & mut self, symbol: Ident, args: & [ Sort ], out: Sort
  ) -> IoResUnit {
    try!( write!(self.writer(), "(declare-fun ") ) ;
    try!( symbol.to_smt2(self.writer()) ) ;
    try!( write!(self.writer(), " ( ") ) ;
    for arg in args {
      try!( arg.to_smt2(self.writer()) ) ;
      try!( write!(self.writer(), " ") )
    } ;
    try!( write!(self.writer(), ") ") ) ;
    try!( out.to_smt2(self.writer()) ) ;
    write!(self.writer(), ")\n\n")
  }
  fn declare_const(
    & mut self, symbol: Ident, out_sort: Sort
  ) -> IoResUnit {
    try!( write!(self.writer(), "(declare-const ") ) ;
    try!( symbol.to_smt2(self.writer()) ) ;
    try!( write!(self.writer(), " ") ) ;
    try!( out_sort.to_smt2(self.writer()) ) ;
    write!(self.writer(), ")\n\n")
  }
  fn define_fun(
    & mut self, symbol: Ident, args: & [ (Ident, Sort) ], out: Sort, body: Expr
  ) -> IoResUnit {
    try!( write!(self.writer(), "(declare-fun ") ) ;
    try!( symbol.to_smt2(self.writer()) ) ;
    try!( write!(self.writer(), " ( ") ) ;
    for arg in args {
      let (ref id, ref sort) = * arg ;
      try!( write!(self.writer(), "(") ) ;
      try!( id.to_smt2(self.writer()) ) ;
      try!( write!(self.writer(), " ") ) ;
      try!( sort.to_smt2(self.writer()) ) ;
      try!( write!(self.writer(), ") ") )
    } ;
    try!( write!(self.writer(), ") ") ) ;
    try!( out.to_smt2(self.writer()) ) ;
    try!( write!(self.writer(), "\n   ") ) ;
    try!( body.to_smt2(self.writer()) ) ;
    write!(self.writer(), "\n)\n\n")
  }
  fn define_funs_rec(
    & mut self, funs: & [ (Ident, & [ (Ident, Sort) ], Sort, Expr) ]
  ) -> IoResUnit {
    // Header.
    try!( write!(self.writer(), "(define-funs-rec (\n") ) ;

    // Signatures.
    for fun in funs {
      let (ref id, ref args, ref out, _) = * fun ;
      try!( write!(self.writer(), "   (") ) ;
      try!( id.to_smt2(self.writer()) ) ;
      try!( write!(self.writer(), " ( ") ) ;
      for arg in * args {
        let (ref arg, ref sort) = * arg ;
        try!( write!(self.writer(), "(") ) ;
        try!( arg.to_smt2(self.writer()) ) ;
        try!( write!(self.writer(), " ") ) ;
        try!( sort.to_smt2(self.writer()) ) ;
        try!( write!(self.writer(), ") ") ) ;
      } ;
      try!( write!(self.writer(), ") ") ) ;
      try!( out.to_smt2(self.writer()) ) ;
      try!( write!(self.writer(), ")\n") )
    } ;
    try!( write!(self.writer(), " ) (") ) ;

    // Bodies
    for fun in funs {
      let (_, _, _, ref body) = * fun ;
      try!( write!(self.writer(), "\n   ") ) ;
      try!( body.to_smt2(self.writer()) )
    } ;
    write!(self.writer(), "\n )\n)\n\n")
  }
  fn define_fun_rec(
    & mut self, symbol: Ident, args: & [ (Ident, Sort) ], out: Sort, body: Expr
  ) -> IoResUnit {
    // Header.
    try!( write!(self.writer(), "(define-fun-rec (\n") ) ;

    // Signature.
    try!( write!(self.writer(), "   (") ) ;
    try!( symbol.to_smt2(self.writer()) ) ;
    try!( write!(self.writer(), " ( ") ) ;
    for arg in args {
      let (ref arg, ref sort) = * arg ;
      try!( write!(self.writer(), "(") ) ;
      try!( arg.to_smt2(self.writer()) ) ;
      try!( write!(self.writer(), " ") ) ;
      try!( sort.to_smt2(self.writer()) ) ;
      try!( write!(self.writer(), ") ") ) ;
    } ;
    try!( write!(self.writer(), ") ") ) ;
    try!( out.to_smt2(self.writer()) ) ;
    try!( write!(self.writer(), ")\n") ) ;
    try!( write!(self.writer(), " ) (") ) ;

    // Body.
    try!( write!(self.writer(), "\n   ") ) ;
    try!( body.to_smt2(self.writer()) ) ;
    write!(self.writer(), "\n )\n)\n\n")
  }

  // |===| Asserting and inspecting formulas.

  fn assert(& mut self, expr: Expr) -> IoResUnit {
    try!( write!(self.writer(), "(assert\n  ") ) ;
    try!( expr.to_smt2(self.writer()) ) ;
    write!(self.writer(), "\n)")
  }
  fn get_assertions(& mut self) -> IoResUnit {
    write!(self.writer(), "(get-assertions)\n\n")
  }

  // |===| Checking for satisfiability.

  fn check_sat(& mut self) -> IoResUnit {
    write!(self.writer(), "(check-sat)\n\n")
  }
  fn check_sat_assuming(& mut self, bool_vars: & [ Ident ]) -> IoResUnit {
    let command = self.check_sat_assuming_command() ;
    try!( write!(self.writer(), "({}\n ", command) );
    for v in bool_vars {
      try!( write!(self.writer(), " ") ) ;
      try!( v.to_smt2(self.writer()) )
    } ;
    write!(self.writer(), "\n)\n\n")
  }

  // |===| Inspecting models.

  fn get_value(& mut self, exprs: & [ Expr ]) -> IoResUnit {
    try!( write!(self.writer(), "(get-value") ) ;
    for e in exprs {
      try!( write!(self.writer(), "\n  ") ) ;
      try!( e.to_smt2(self.writer()) )
    } ;
    write!(self.writer(), "\n)\n\n")
  }
  fn get_assignment(& mut self) -> IoResUnit {
    write!(self.writer(), "(get-assignment)\n\n")
  }
  fn get_model(& mut self) -> IoResUnit {
    write!(self.writer(), "(get-model)\n\n")
  }

  // |===| Inspecting proofs.

  fn get_unsat_assumptions(& mut self) -> IoResUnit {
    write!(self.writer(), "(get-unsat-assumptions)\n\n")
  }
  fn get_proof(& mut self) -> IoResUnit {
    write!(self.writer(), "(get-proof)\n\n")
  }
  fn get_unsat_core(& mut self) -> IoResUnit {
    write!(self.writer(), "(get-unsat-core)\n\n")
  }

  // |===| Inspecting settings.

  fn get_info(& mut self, flag: & str) -> IoResUnit {
    write!(self.writer(), "(get-info {})\n\n", flag)
  }
  fn get_option(& mut self, option: & str) -> IoResUnit {
    write!(self.writer(), "(get-option {})\n\n", option)
  }

  // |===| Script information.

  fn set_info(& mut self, attribute: & str) -> IoResUnit {
    write!(self.writer(), "(set-info {})\n\n", attribute)
  }
  fn echo(& mut self, text: & str) -> IoResUnit {
    write!(self.writer(), "(echo \"{}\")\n\n", text)
  }
}