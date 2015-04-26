#![ doc = "
Parsers for the different solvers.
"]

use parser_combinators::{
  spaces, many1, sep_by, digit, satisfy, Parser, ParserExt, ParseError
} ;

use ::common::* ;

pub trait GenericParser<Ident, Value, Expr, Proof> : {

  fn parse_assertions(& mut self)

}