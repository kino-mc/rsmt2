#![ doc = "
Printers for the different solvers.
"]

use std::io::{Write} ;

use ::conf::SolverConf ;
use ::common::* ;

pub trait GenericPrinter<
  Ident: Printable,
  Sort: Printable,
  Expr: Printable,
> : Writable {

  fn comment(
    & mut self, _: & SolverConf, lines: ::std::str::Lines
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    for line in lines { try!( write!(writer, ";; {}\n", line) ) } ;
    write!(writer, "\n")
  }

  // |===| (Re)starting and terminating.

  fn reset(
    & mut self, _: & SolverConf
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(reset)\n\n")
  }
  fn set_logic(
    & mut self, _: & SolverConf, logic: & Logic
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    try!( write!(writer, "(set-logic ") ) ;
    try!( logic.to_smt2(writer) ) ;
    write!(writer, ")\n\n")
  }
  fn set_option(
    & mut self, _: & SolverConf, option: & str, value: & str
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(set-option {} {})\n\n", option, value)
  }
  fn exit(
    & mut self, _: & SolverConf
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(exit)\n")
  }

  // |===| Modifying the assertion stack.

  fn push(
    & mut self, _: & SolverConf, n: & u8
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(push {})\n\n", n)
  }
  fn pop(
    & mut self, _: & SolverConf, n: & u8
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(pop {})\n\n", n)
  }
  fn reset_assertions(
    & mut self, _: & SolverConf
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(reset-assertions)\n\n")
  }

  // |===| Introducing new symbols.

  fn declare_sort(
    & mut self, _: & SolverConf, sort: Sort, arity: & u8
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    try!( write!(writer, "(declare-sort ") ) ;
    try!( sort.to_smt2(writer) ) ;
    write!(writer, " {})\n\n", arity)
  }
  fn define_sort(
    & mut self, _: & SolverConf, sort: Sort, args: & [ Expr ], body: Expr
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    try!( write!(writer, "( define-sort ") ) ;
    try!( sort.to_smt2(writer) ) ;
    try!( write!(writer, "\n   ( ") ) ;
    for arg in args {
      try!( arg.to_smt2(writer) ) ;
      try!( write!(writer, " ") )
    } ;
    try!( write!(writer, ")\n   ") ) ;
    try!( body.to_smt2(writer) ) ;
    write!(writer, "\n)\n\n")
  }
  fn declare_fun(
    & mut self, _: & SolverConf, symbol: Ident, args: & [ Sort ], out: Sort
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    try!( write!(writer, "(declare-fun ") ) ;
    try!( symbol.to_smt2(writer) ) ;
    try!( write!(writer, " ( ") ) ;
    for arg in args {
      try!( arg.to_smt2(writer) ) ;
      try!( write!(writer, " ") )
    } ;
    try!( write!(writer, ") ") ) ;
    try!( out.to_smt2(writer) ) ;
    write!(writer, ")\n\n")
  }
  fn declare_const(
    & mut self, _: & SolverConf, symbol: Ident, out_sort: Sort
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    try!( write!(writer, "(declare-const ") ) ;
    try!( symbol.to_smt2(writer) ) ;
    try!( write!(writer, " ") ) ;
    try!( out_sort.to_smt2(writer) ) ;
    write!(writer, ")\n\n")
  }
  fn define_fun(
    & mut self, _: & SolverConf,
    symbol: Ident, args: & [ (Ident, Sort) ], out: Sort, body: Expr
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    try!( write!(writer, "(declare-fun ") ) ;
    try!( symbol.to_smt2(writer) ) ;
    try!( write!(writer, " ( ") ) ;
    for arg in args {
      let (ref id, ref sort) = * arg ;
      try!( write!(writer, "(") ) ;
      try!( id.to_smt2(writer) ) ;
      try!( write!(writer, " ") ) ;
      try!( sort.to_smt2(writer) ) ;
      try!( write!(writer, ") ") )
    } ;
    try!( write!(writer, ") ") ) ;
    try!( out.to_smt2(writer) ) ;
    try!( write!(writer, "\n   ") ) ;
    try!( body.to_smt2(writer) ) ;
    write!(writer, "\n)\n\n")
  }
  fn define_funs_rec(
    & mut self, _: & SolverConf,
    funs: & [ (Ident, & [ (Ident, Sort) ], Sort, Expr) ]
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    // Header.
    try!( write!(writer, "(define-funs-rec (\n") ) ;

    // Signatures.
    for fun in funs {
      let (ref id, ref args, ref out, _) = * fun ;
      try!( write!(writer, "   (") ) ;
      try!( id.to_smt2(writer) ) ;
      try!( write!(writer, " ( ") ) ;
      for arg in * args {
        let (ref arg, ref sort) = * arg ;
        try!( write!(writer, "(") ) ;
        try!( arg.to_smt2(writer) ) ;
        try!( write!(writer, " ") ) ;
        try!( sort.to_smt2(writer) ) ;
        try!( write!(writer, ") ") ) ;
      } ;
      try!( write!(writer, ") ") ) ;
      try!( out.to_smt2(writer) ) ;
      try!( write!(writer, ")\n") )
    } ;
    try!( write!(writer, " ) (") ) ;

    // Bodies
    for fun in funs {
      let (_, _, _, ref body) = * fun ;
      try!( write!(writer, "\n   ") ) ;
      try!( body.to_smt2(writer) )
    } ;
    write!(writer, "\n )\n)\n\n")
  }
  fn define_fun_rec(
    & mut self, _: & SolverConf,
    symbol: Ident, args: & [ (Ident, Sort) ], out: Sort, body: Expr
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    // Header.
    try!( write!(writer, "(define-fun-rec (\n") ) ;

    // Signature.
    try!( write!(writer, "   (") ) ;
    try!( symbol.to_smt2(writer) ) ;
    try!( write!(writer, " ( ") ) ;
    for arg in args {
      let (ref arg, ref sort) = * arg ;
      try!( write!(writer, "(") ) ;
      try!( arg.to_smt2(writer) ) ;
      try!( write!(writer, " ") ) ;
      try!( sort.to_smt2(writer) ) ;
      try!( write!(writer, ") ") ) ;
    } ;
    try!( write!(writer, ") ") ) ;
    try!( out.to_smt2(writer) ) ;
    try!( write!(writer, ")\n") ) ;
    try!( write!(writer, " ) (") ) ;

    // Body.
    try!( write!(writer, "\n   ") ) ;
    try!( body.to_smt2(writer) ) ;
    write!(writer, "\n )\n)\n\n")
  }

  // |===| Asserting and inspecting formulas.

  fn assert(
    & mut self, _: & SolverConf, expr: Expr
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    try!( write!(writer, "(assert\n  ") ) ;
    try!( expr.to_smt2(writer) ) ;
    write!(writer, "\n)")
  }
  fn get_assertions(
    & mut self, _: & SolverConf
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(get-assertions)\n\n")
  }

  // |===| Checking for satisfiability.

  fn check_sat(
    & mut self, _: & SolverConf
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(check-sat)\n\n")
  }
  fn check_sat_assuming(
    & mut self, conf: & SolverConf, bool_vars: & [ Ident ]
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    try!( write!(writer, "({}\n ", conf.check_sat_assuming) );
    for v in bool_vars {
      try!( write!(writer, " ") ) ;
      try!( v.to_smt2(writer) )
    } ;
    write!(writer, "\n)\n\n")
  }

  // |===| Inspecting models.

  fn get_value(
    & mut self, _: & SolverConf, exprs: & [ Expr ]
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    try!( write!(writer, "(get-value") ) ;
    for e in exprs {
      try!( write!(writer, "\n  ") ) ;
      try!( e.to_smt2(writer) )
    } ;
    write!(writer, "\n)\n\n")
  }
  fn get_assignment(
    & mut self, _: & SolverConf
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(get-assignment)\n\n")
  }
  fn get_model(
    & mut self, _: & SolverConf
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(get-model)\n\n")
  }

  // |===| Inspecting proofs.

  fn get_unsat_assumptions(
    & mut self, _: & SolverConf
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(get-unsat-assumptions)\n\n")
  }
  fn get_proof(
    & mut self, _: & SolverConf
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(get-proof)\n\n")
  }
  fn get_unsat_core(
    & mut self, _: & SolverConf
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(get-unsat-core)\n\n")
  }

  // |===| Inspecting settings.

  fn get_info(
    & mut self, _: & SolverConf, flag: & str
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(get-info {})\n\n", flag)
  }
  fn get_option(
    & mut self, _: & SolverConf, option: & str
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(get-option {})\n\n", option)
  }

  // |===| Script information.

  fn set_info(
    & mut self, _: & SolverConf, attribute: & str
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(set-info {})\n\n", attribute)
  }
  fn echo(
    & mut self, _: & SolverConf, text: & str
  ) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(echo \"{}\")\n\n", text)
  }
}