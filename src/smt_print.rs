#![ doc = "
The `Smt2Printer` trait provides functions to write SMT lib 2 commands to some
writer.
"]

use std::io::Write ;

use ::common::* ;

trait InnerSmt2Print {

  /// The writer to print the commands to.
  #[inline]
  fn writer(& mut self) -> & mut Write ;

}

impl<
  Symbol: Printable,
  Sort: Printable,
  Expr: Printable
> Smt2Print<Symbol, Sort, Expr> for InnerSmt2Print {

  /// Prints a comment.
  fn comment(& mut self, lines: ::std::str::Lines) -> IoResUnit {
    let mut writer = self.writer() ;
    for line in lines {
      try!(write!(writer, ";; {}\n", line))
    }
    Ok(())
  }


  fn reset(& mut self) -> IoResUnit {
    let mut writer = self.writer() ;
    write!(writer, "(reset)")
  }

  fn set_logic(& mut self, logic: & Logic) -> IoResUnit {
    let mut writer = self.writer() ;
    try!(write!(writer, "(set-logic ")) ;
    try!(logic.to_smt2(writer)) ;
    write!(writer, " )\n")
  }

  fn set_option(& mut self, option: & str, value: & str) -> IoResUnit {Ok(())}

  fn exit(& mut self) -> IoResUnit {Ok(())}



  // |===| Modifying the assertion stack.


  fn push(& mut self, n: & u8) -> IoResUnit {Ok(())}

  fn pop(& mut self, n: & u8) -> IoResUnit {Ok(())}

  fn reset_assertions(& mut self) -> IoResUnit {Ok(())}



  // |===| Introducing new symbols.


  fn declare_sort(& mut self, sort: Sort, arity: & u8) -> IoResUnit {Ok(())}
  
  fn define_sort(
    & mut self, sort: Sort, args: & [ Expr ], body: Expr
  ) -> IoResUnit {Ok(())}

  fn declare_fun(
    & mut self, symbol: & str, in_sorts: & [ Sort ], out_sort: Sort
  ) -> IoResUnit {Ok(())}

}