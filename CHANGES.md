# v0.9.0

- long overdue update of the `errors`
- macros `smtry_io` and `smt_cast_io` are gone because `std::io` errors are
  rsmt2 errors now
- `Solver` commands are now much more generic ; all type parameters are
  separated and all collections are supported
- much cleaner interface, all the commands are in the `Solver` trait now

# v0.6.0

- trait `Expr2Smt` does not use dispatch anymore