# v0.9.6

- `define_const` and `define_const_with`

# v0.9.5

- simplified the workflow significantly
- all solver commands that take info, like `assert`, now take no info; use
  `..._with`, like `assert_with`, to pass down information
- added `declare-datatypes`

# v0.9.2

- fixed problem in `get_values` result parsing

# v0.9.1

- the info used by `*2Smt` is not explicitely a reference anymore
- all solver commands that take an info now have a `<fn_name>_u` version that
  omits the info when it's unit `()`
- added an API for activation literals
- simplified parse traits type parameters a bit

# v0.9.0

- long overdue update of the `errors`
- macros `smtry_io` and `smt_cast_io` are gone because `std::io` errors are
  lifted to `rsmt2` errors now
- `Solver` commands are now much more generic ; all type parameters are
  separated and all collections are supported through iterators
- streamlined the interface, all the commands are in the `Solver` trait now
- support solvers returning `unknown` to check-sat queries

# v0.6.0

- trait `Expr2Smt` does not use dispatch anymore