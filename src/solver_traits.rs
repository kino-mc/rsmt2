#![ doc = "
Interfaces for solvers.
"]

use ::common::* ;


pub trait Smt2Solver<
  Ident,
  Value,
  Sort,
  Expr,
  Proof,
>:  Smt2Print +
    Smt2Parse<Ident, Value, Expr, Proof> +
    Smt2GetNow<Ident, Value, Sort, Expr, Proof> {
}

/** Can print SMT lib 2 commands. */
pub trait Smt2Print {

  /** Prints some string as a comment. */
  fn comment(& mut self, lines: & str) -> IoResUnit ;

  /** Prints some lines as comments. */
  fn comments(& mut self, lines: ::std::str::Lines) -> IoResUnit ;

  // |===| (Re)starting and terminating.

  /** Prints a `reset` command. */
  fn reset(& mut self) -> IoResUnit ;
  /** Prints a `set-logic` command. */
  fn set_logic(& mut self, logic: & Logic) -> IoResUnit ;
  /** Prints a `set-option` command. */
  fn set_option(& mut self, option: & str, value: & str) -> IoResUnit ;
  /** Prints an `exit` command. */
  fn exit(& mut self) -> IoResUnit ;

  // |===| Modifying the assertion stack.

  /** Prints a `push` command. */
  fn push(& mut self, n: & u8) -> IoResUnit ;
  /** Prints a `pop` command. */
  fn pop(& mut self, n: & u8) -> IoResUnit ;
  /** Prints a `reset-assertions` command. */
  fn reset_assertions(& mut self) -> IoResUnit ;

  // |===| Introducing new symbols.

  /** Prints a `declare-sort` command. */
  fn declare_sort<Sort: Printable>(
    & mut self, sort: Sort, arity: & u8
  ) -> IoResUnit ;
  /** Prints a `define-sort` command. */
  fn define_sort<Sort: Printable, Expr: Printable>(
    & mut self, sort: Sort, args: & [ Expr ], body: Expr
  ) -> IoResUnit ;
  /** Prints a `declare-fun` command. */
  fn declare_fun<Sort: Printable, Ident: Printable>(
    & mut self, symbol: Ident, in_sorts: & [ Sort ], out_sort: Sort
  ) -> IoResUnit ;
  /** Prints a `declare-const` command. */
  fn declare_const<Sort: Printable, Ident: Printable>(
    & mut self, symbol: Ident, out_sort: Sort
  ) -> IoResUnit ;
  /** Prints a `define-fun` command. */
  fn define_fun<Sort: Printable, Ident: Printable, Expr: Printable>(
    & mut self, symbol: Ident, args: & [ (Ident, Sort) ], out: Sort, body: Expr
  ) -> IoResUnit ;
  /** Prints a `define-funs-rec` command. */
  fn define_funs_rec<Sort: Printable, Ident: Printable, Expr: Printable>(
    & mut self, funs: & [ (Ident, & [ (Ident, Sort) ], Sort, Expr) ]
  ) -> IoResUnit ;
  /** Prints a `define-fun-rec` command. */
  fn define_fun_rec<Sort: Printable, Ident: Printable, Expr: Printable>(
    & mut self, symbol: Ident, args: & [ (Ident, Sort) ], out: Sort, body: Expr
  ) -> IoResUnit ;

  // |===| Asserting and inspecting formulas.

  /** Prints an `assert` command. */
  fn assert<Expr: Printable>(& mut self, expr: Expr) -> IoResUnit ;
  /** Prints an `get-assertions` command. */
  fn get_assertions(& mut self) -> IoResUnit ;

  // |===| Checking for satisfiability.

  /** Prints a `check-sat` command. */
  fn check_sat(& mut self) -> IoResUnit ;
  /** Prints a `check-sat-assuming` command. */
  fn check_sat_assuming<Ident: Printable>(
    & mut self, bool_vars: & [ Ident ]
  ) -> IoResUnit ;

  // |===| Inspecting models.

  /** Prints a `get-value` command. */
  fn get_value<Expr: Printable>(& mut self, exprs: & [ Expr ]) -> IoResUnit ;
  /** Prints a `get-assignment` command. */
  fn get_assignment(& mut self) -> IoResUnit ;
  /** Prints a `get-model` command. */
  fn get_model(& mut self) -> IoResUnit ;

  // |===| Inspecting proofs.

  /** Prints a `get-unsat-assumptions` command. */
  fn get_unsat_assumptions(& mut self) -> IoResUnit ;
  /** Prints a `get-unsat-assumptions` command. */
  fn get_proof(& mut self) -> IoResUnit ;
  /** Prints a `get-unsat-assumptions` command. */
  fn get_unsat_core(& mut self) -> IoResUnit ;

  // |===| Inspecting settings.

  /** Prints a `get-info` command. */
  fn get_info(& mut self, flag: & str) -> IoResUnit ;
  /** Prints a `get-option` command. */
  fn get_option(& mut self, option: & str) -> IoResUnit ;

  // |===| Script information.

  /** Prints a `set-info` command. */
  fn set_info(& mut self, attribute: & str) -> IoResUnit ;
  /** Prints an `echo` command. */
  fn echo(& mut self, text: & str) -> IoResUnit ;
}


/** Can parse the result of SMT lib 2 queries. */
pub trait Smt2Parse<Ident, Value, Expr, Proof> {

  /** Parses a `success` result. */
  fn parse_success(& mut self) -> IoResUnit ;

  /** Parses the result of a `get-assertion` query. */
  fn parse_assertions(& mut self) -> IoRes<Option<Vec<Expr>>> ;

  /** Parses the result of a `check-sat` or `check-sat-assuming` query. */
  fn parse_check_sat(& mut self) -> IoResBool ;

  /** Parses the result of a `get-value` query. */
  fn parse_value(& mut self) -> IoRes<Option<Vec<Value>>> ;
  /** Parses the result of a `get-assignment` query. */
  fn parse_assignment(& mut self) -> IoRes<Option<Vec<(Ident, Value)>>> ;
  /** Parses the result of a `get-model` query. */
  fn parse_model(& mut self) -> IoRes<Option<Vec<(Ident, Value)>>> ;

  /** Parses the result of a `get-unsat-assumptions` query. */
  fn parse_unsat_assumptions(& mut self) -> IoRes<Option<Vec<Ident>>> ;
  /** Parses the result of a `get-proof` query. */
  fn parse_proof(& mut self) -> IoRes<Option<Proof>> ;
  /** Parses the result of a `get-unsat-core` query. */
  fn parse_unsat_core(& mut self) -> IoRes<Option<Vec<Ident>>> ;

  /** Parses the result of a `get-info` query. */
  fn parse_info(& mut self) -> IoRes<Option<String>> ;
  /** Parses the result of a `get-option` query. */
  fn parse_option(& mut self) -> IoRes<Option<String>> ;

}

/** Can issue an SMT lib 2 query and parse its result. */
pub trait Smt2GetNow<
  Ident: Printable,
  Value,
  Sort: Printable,
  Expr: Printable,
  Proof
> : Smt2Print + Smt2Parse<Ident, Value, Expr, Proof> {

  /** Issues a `get-assertion` query and parses the result. */
  fn get_assertions_now(& mut self) -> IoRes<Option<Vec<Expr>>> {
    try!(self.get_assertions()) ;
    self.parse_assertions()
  }

  /** Issues a `check-sat` query and parses the result. */
  fn check_sat_now(& mut self) -> IoResBool {
    try!(self.check_sat()) ;
    self.parse_check_sat()
  }
  /** Issues a `check-sat-assuming` query and parses the result. */
  fn check_sat_assuming_now(& mut self, bool_vars: & [ Ident ]) -> IoResBool {
    try!(self.check_sat_assuming(bool_vars)) ;
    self.parse_check_sat()
  }

  /** Issues a `get-value` query and parses the result. */
  fn get_value_now(
    & mut self, exprs: & [ Expr ]
  ) -> IoRes<Option<Vec<Value>>> {
    try!(self.get_value(exprs)) ;
    self.parse_value()
  }
  /** Issues a `get-assignment` query and parses the result. */
  fn get_assignment_now(& mut self) -> IoRes<Option<Vec<(Ident, Value)>>> {
    try!(self.get_assignment()) ;
    self.parse_assignment()
  }
  /** Issues a `get-model` query and parses the result. */
  fn get_model_now(& mut self) -> IoRes<Option<Vec<(Ident, Value)>>> {
    try!(self.get_model()) ;
    self.parse_model()
  }

  /** Issues a `get-unsat-assumptions` query and parses the result. */
  fn get_unsat_assumptions_now(& mut self) -> IoRes<Option<Vec<Ident>>> {
    try!(self.get_unsat_assumptions()) ;
    self.parse_unsat_assumptions()
  }
  /** Issues a `get-proof` query and parses the result. */
  fn get_proof_now(& mut self) -> IoRes<Option<Proof>> {
    try!(self.get_proof()) ;
    self.parse_proof()
  }
  /** Issues a `get-unsat-core` query and parses the result. */
  fn get_unsat_core_now(& mut self) -> IoRes<Option<Vec<Ident>>> {
    try!(self.get_unsat_core()) ;
    self.parse_unsat_core()
  }

  /** Issues a `get-info` query and parses the result. */
  fn get_info_now(& mut self, flag: & str) -> IoRes<Option<String>> {
    try!(self.get_info(flag)) ;
    self.parse_info()
  }
  /** Issues a `get-option` query and parses the result. */
  fn get_option_now(& mut self, option: & str) -> IoRes<Option<String>> {
    try!(self.get_option(option)) ;
    self.parse_option()
  }

}