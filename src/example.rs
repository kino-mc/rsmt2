//! A simple example of using `rsmt2`.


// Parser library.
use std::io::Write ;

use * ;
use to_smt::* ;
use parse::* ;

use self::Var::* ;


/// A type.
#[derive(Debug,Clone,Copy,PartialEq)]
enum Type {
  /// Integers.
  Int,
  /// Booleans.
  Bool,
  /// Reals.
  Real,
}
impl Type {
  /// String representation.
  pub fn to_str(& self) -> & 'static str {
    match * self {
      Type::Int => "Int",
      Type::Bool => "Bool",
      Type::Real => "Real",
    }
  }
}
impl Sort2Smt for Type {
  fn sort_to_smt2<Writer: Write>(
    & self, writer: & mut Writer
  ) -> SmtRes<()> {
    writer.write_all( self.to_str().as_bytes() ) ? ;
    Ok(())
  }
}




/// A symbol is a variable and an offset.
#[derive(Debug,Clone,PartialEq)]
pub struct Symbol<'a, 'b>(& 'a Var, & 'b Offset) ;




/// An offset gives the index of current and next step.
#[derive(Debug,Clone,Copy,PartialEq)]
pub struct Offset(usize, usize) ;
impl Offset {
  /// Index of the current state.
  #[inline(always)]
  pub fn curr(& self) -> usize { self.0 }
  /// Index of the next state.
  #[inline(always)]
  pub fn next(& self) -> usize { self.1 }
}


/// An unrolled version of something.
#[derive(Debug,Clone,PartialEq)]
pub struct Unrolled<'a, T>(T, & 'a Offset) ;


/// Under the hood a symbol is a string.
pub type Sym = String ;



/// A variable wraps a symbol.
#[derive(Debug,Clone,PartialEq)]
pub enum Var {
  /// Variable constant in time (Non-Stateful Var: NSVar).
  NSVar(Sym),
  /// State variable in the current step.
  SVar0(Sym),
  /// State variable in the next step.
  SVar1(Sym),
}
impl Var {
  /// Symbol of a variable.
  pub fn sym(& self) -> & str {
    match * self { NSVar(ref s) => s, SVar0(ref s) => s, SVar1(ref s) => s }
  }
  /// Non-stateful variable constructor.
  pub fn nsvar(s: & str) -> Self { NSVar(s.to_string()) }
  /// State variable in the current step.
  pub fn svar0(s: & str) -> Self { SVar0(s.to_string()) }
  /// State variable in the next step.
  pub fn svar1(s: & str) -> Self { SVar1(s.to_string()) }

  /// Given an offset, an S-expression can be unrolled.
  pub fn unroll<'a, 'b>(
    & 'a self, off: & 'b Offset
  ) -> Unrolled<'b, & 'a Var> {
    Unrolled(self, off)
  }
}

impl<'a, V: AsRef<Var>> Expr2Smt<()> for Unrolled<'a, V> {
  fn expr_to_smt2<Writer: Write>(
    & self, writer: & mut Writer, _: ()
  ) -> SmtRes<()> {
    self.0.as_ref().expr_to_smt2(writer, & self.1)
  }
}
impl<'a> Expr2Smt<& 'a Offset> for Var {
  fn expr_to_smt2<Writer: Write>(
    & self, writer: & mut Writer, off: & 'a Offset
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
}

impl<'a> Sym2Smt<& 'a Offset> for Var {
  fn sym_to_smt2<Writer: Write>(
    & self, writer: & mut Writer, off: & 'a Offset
  ) -> SmtRes<()> {
    self.expr_to_smt2(writer, off)
  }
}
impl<'a, 'b> Sym2Smt<()> for Unrolled<'a, & 'b Var> {
  fn sym_to_smt2<Writer: Write>(
    & self, writer: & mut Writer, _: ()
  ) -> SmtRes<()> {
    self.0.expr_to_smt2(writer, & self.1)
  }
}



/// A constant.
#[derive(Debug,Clone,PartialEq)]
pub enum Const {
  /// Boolean constant.
  BConst(bool),
  /// Integer constant.
  IConst(isize),
  /// Rational constant.
  RConst(isize,usize),
}

impl Expr2Smt<()> for Const {
  fn expr_to_smt2<Writer: Write>(
    & self, writer: & mut Writer, _: ()
  ) -> SmtRes<()> {
    match * self {
      Const::BConst(b) => write!(writer, "{}", b) ?,
      Const::IConst(i) => {
        let neg = i < 0 ;
        if neg { write!(writer, "(- ") ? }
        write!(writer, "{}", i.abs()) ? ;
        if neg { write!(writer, ")") ? }
      },
      Const::RConst(num, den) => {
        let neg = num < 0 ;
        if neg { write!(writer, "(- ") ? }
        write!(writer, "(/ {} {})", num, den) ? ;
        if neg { write!(writer, ")") ? }
      },
    }
    Ok(())
  }
}




/// An S-expression.
#[derive(Debug,Clone,PartialEq)]
pub enum SExpr {
  /// A variable.
  Id(Var),
  /// A constant.
  Val(Const),
  /// An application of function symbol.
  App(Sym, Vec<SExpr>),
}

impl SExpr {
  /// Application constructor.
  pub fn app(sym: & str, args: Vec<SExpr>) -> Self {
    SExpr::App(sym.to_string(), args)
  }
  /// Given an offset, an S-expression can be unrolled.
  pub fn unroll<'a, 'b>(
    & 'a self, off: & 'b Offset
  ) -> Unrolled<'b, & 'a SExpr> {
    Unrolled(self, off)
  }
}

impl<'a> Expr2Smt<& 'a Offset> for SExpr {
  fn expr_to_smt2<Writer: Write>(
    & self, writer: & mut Writer, off: & 'a Offset
  ) -> SmtRes<()> {
    match * self {
      SExpr::Id(ref var) => var.expr_to_smt2(writer, off),
      SExpr::Val(ref cst) => cst.expr_to_smt2(writer, ()),
      SExpr::App(ref sym, ref args) => {
        write!(writer, "({}", sym) ? ;
        for arg in args {
          write!(writer, " ") ? ;
          arg.expr_to_smt2(writer, off) ?
        }
        write!(writer, ")") ? ;
        Ok(())
      }
    }
  }
}

impl<'a, 'b> Expr2Smt<()> for Unrolled<'a, & 'b SExpr> {
  fn expr_to_smt2<Writer: Write>(
    & self, writer: & mut Writer, _: ()
  ) -> SmtRes<()> {
    self.0.expr_to_smt2(writer, & self.1)
  }
}





/// Empty parser structure.
#[derive(Clone, Copy)]
pub struct Parser ;

impl<'a> IdentParser< (Var, Option<usize>), Type, & 'a str > for Parser {
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

impl<'a, Br> ValueParser< Const, & 'a mut SmtParser<Br> > for Parser
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




/// Convenience macro.
#[cfg(test)]
macro_rules! smtry {
  ($e:expr, failwith $( $msg:expr ),+) => (
    match $e {
      Ok(something) => something,
      Err(e) => panic!( $($msg),+ , e)
    }
  ) ;
}


#[cfg(test)]
fn get_solver<Parser>(p: Parser) -> Solver<Parser> {
  use conf::SolverConf ;
  let conf = SolverConf::z3() ;
  match Solver::new(conf, p) {
    Ok(solver) => solver,
    Err(e) => panic!("Could not spawn solver solver: {:?}", e)
  }
}


#[test]
fn declare_non_nullary_fun() {
  let mut solver = get_solver(Parser) ;

  smtry!(
    solver.declare_fun(
      "my_fun", & [ "Int", "Real", "Bool" ], "Real"
    ), failwith "during function declaration: {:?}"
  ) ;

  solver.kill().expect("kill")
}




#[test]
fn test_native() {
  use self::SExpr::* ;

  let mut solver = get_solver(Parser) ;

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

  smtry!(
    solver.declare_const_with(& nsv_0, & "Bool", & offset1),
    failwith "declaration failed: {:?}"
  ) ;

  smtry!(
    solver.declare_const_with(& nsv_1, & "Real", & offset1),
    failwith "declaration failed: {:?}"
  ) ;

  smtry!(
    solver.declare_const_with(& sv_0, & "Bool", & offset1),
    failwith "declaration failed: {:?}"
  ) ;

  smtry!(
    solver.declare_const_with(& sv_1, & "Int", & offset1),
    failwith "declaration failed: {:?}"
  ) ;

  smtry!(
    solver.assert_with(& app, & offset1),
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

  solver.kill().expect("kill")
}





#[test]
fn test_unroll() {
  use self::SExpr::* ;
  
  let mut solver = get_solver(Parser) ;

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

  let sym = nsv_0.unroll(& offset1) ;
  smtry!(
    solver.declare_const(& sym, & "Bool"),
    failwith "declaration failed: {:?}"
  ) ;

  let sym = nsv_1.unroll(& offset1) ;
  smtry!(
    solver.declare_const(& sym, & "Real"),
    failwith "declaration failed: {:?}"
  ) ;

  let sym = sv_0.unroll(& offset1) ;
  smtry!(
    solver.declare_const(& sym, & "Bool"),
    failwith "declaration failed: {:?}"
  ) ;

  let sym = sv_1.unroll(& offset1) ;
  smtry!(
    solver.declare_const(& sym, & "Int"),
    failwith "declaration failed: {:?}"
  ) ;

  let expr = app.unroll(& offset1) ;
  smtry!(
    solver.assert(& expr),
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

  solver.kill().expect("kill")
}



/// A simple example that does not use information during printing.
pub mod simple {
  use to_smt::Expr2Smt ;
  use parse::{ IdentParser, ValueParser } ;
  use errors::SmtRes ;

  /// Operators. Just implements `Display`, never manipulated directly by the
  /// solver.
  #[derive(Copy, Clone)]
  pub enum Op {
    Add, Sub, Mul, Conj, Disj, Eql, Ge, Gt, Lt, Le,
  }
  impl ::std::fmt::Display for Op {
    fn fmt(& self, w: & mut ::std::fmt::Formatter) -> ::std::fmt::Result {
      w.write_str(
        match * self {
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
        }
      )
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
    fn fmt(& self, w: & mut ::std::fmt::Formatter) -> ::std::fmt::Result {
      match * self {
        Cst::B(b) => write!(w, "{}", b),
        Cst::I(i) if i >= 0 => write!(w, "{}", i),
        Cst::I(i) => write!(w, "(- {})", - i),
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
    O( Op, Vec<Expr> ),
  }
  impl Expr {
    pub fn cst<C: Into<Cst>>(c: C) -> Self {
      Expr::C( c.into() )
    }
  }
  impl Expr2Smt<()> for Expr {
    fn expr_to_smt2<Writer>(
      & self, w: & mut Writer, _: ()
    ) -> SmtRes<()>
    where Writer: ::std::io::Write {
      let mut stack = vec![ (false, vec![self], false) ] ;
      while let Some((space, mut to_write, closing_paren)) = stack.pop() {
        if let Some(next) = to_write.pop() {
          if space {
            write!(w, " ") ?
          }
          // We have something to print, push the rest back.
          stack.push((space, to_write, closing_paren)) ;
          match * next {
            Expr::C(cst) => write!(w, "{}", cst) ?,
            Expr::V(ref var) => write!(w, "{}", var) ?,
            Expr::O(op, ref sub_terms) => {
              write!(w, "({}", op) ? ;
              stack.push((true, sub_terms.iter().rev().collect(), true))
            },
          }
        } else {
          // No more things to write at this level.
          if closing_paren {
            write!(w, ")") ?
          }
        }
      }
      Ok(())
    }
  }


  /// Empty parser structure, we will not maintain any context.
  #[derive(Clone, Copy)]
  pub struct Parser ;
  impl<'a> IdentParser<String, String, & 'a str> for Parser {
    fn parse_ident(self, input: & 'a str) -> SmtRes<String> {
      Ok( input.to_string() )
    }
    fn parse_type(self, input: & 'a str) -> SmtRes<String> {
      match input {
        "Int" => Ok( "Int".into() ),
        "Bool" => Ok( "Bool".into() ),
        sort => bail!("unexpected sort `{}`", sort),
      }
    }
  }
  impl<'a> ValueParser<Cst, & 'a str> for Parser {
    fn parse_value(self, input: & 'a str) -> SmtRes<Cst> {
      match input.trim() {
        "true" => Ok( Cst::B(true) ),
        "false" => Ok( Cst::B(false) ),
        int => {
          use std::str::FromStr ;
          let s = int.trim() ;
          if let Ok(res) = isize::from_str(s) {
            return Ok( Cst::I(res) )
          } else if s.len() >= 4 {
            if & s[0 .. 1] == "("
            && & s[s.len() - 1 ..] == ")" {
              let s = & s[1 .. s.len() - 1].trim() ;
              if & s[0 .. 1] == "-" {
                let s = & s[1..].trim() ;
                if let Ok(res) = isize::from_str(s) {
                  return Ok( Cst::I(- res) )
                }
              }
            }
          }
          bail!("unexpected value `{}`", int)
        },
      }
    }
  }


  #[test]
  fn run() {
    let mut solver = ::example::get_solver(Parser) ;

    let v_1 = "v_1".to_string() ;
    let v_2 = "v_2".to_string() ;

    solver.declare_const( & v_1, & "Bool" ).expect(
      "while declaring v_1"
    ) ;
    solver.declare_const( & v_2, & "Int" ).expect(
      "while declaring v_2"
    ) ;

    let expr = Expr::O(
      Op::Disj, vec![
        Expr::O(
          Op::Ge, vec![ Expr::cst(-7), Expr::V( v_2.clone() ) ]
        ),
        Expr::V( v_1.clone() )
      ]
    ) ;

    solver.assert( & expr ).expect(
      "while asserting an expression"
    ) ;

    if solver.check_sat().expect("during check sat") {

      let model = solver.get_model_const().expect(
        "while getting model"
      ) ;

      let mut okay = false ;
      for (ident, typ, value) in model {
        if ident == v_1 {
          assert_eq!( typ, "Bool" ) ;
          match value {
            Cst::B(true) => okay = true,
            Cst::B(false) => (),
            Cst::I(int) => panic!(
              "value for v_1 is `{}`, expected boolean", int
            ),
          }
        } else if ident == v_2 {
          assert_eq!( typ, "Int" ) ;
          match value {
            Cst::I(i) if -7 >= i => okay = true,
            Cst::I(_) => (),
            Cst::B(b) => panic!(
              "value for v_2 is `{}`, expected isize", b
            ),
          }
        }
      }

      if ! okay {
        panic!("got sat, but model is spurious")
      }

    } else {
      panic!("expected sat, got unsat")
    }

    solver.kill().expect("killing solver")

  }


}