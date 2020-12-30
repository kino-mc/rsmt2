# v0.11.0

- a lot of documentation fixes/improvements
- asynchronous check-sat-s, see `asynch` module and `Solver::async_check_sat_or_unk`

# v0.11.0-beta.3

- `SmtConf` and `Solver` creation now take a mandatory command argument to run the solver
    - using default command for the solvers is not recommended as it is end-user-dependent and not
      flexible
    - if you still wish to use default commands, use the `default_<solver>` functions provided for
      `SmtConf` and `Solver`, *e.g.* `Solver::default_z3()`
- added example [`examples/custom_cmd.rs`][custom cmd example] demonstrating how to pass a custom
    command to a solver configuration
- `Solver` now implements [`std::io::Read`][std read] in addition to [`std::io::Write`][std write]
    - useful for performing custom queries and quick testing
- added a `prelude` module containing common imports for convenience

[custom cmd example]: ./examples/custom_cmd.rs (Custom command example)
[std read]: https://doc.rust-lang.org/std/io/trait.Read.html (Read trait on Rust std)
[std write]: https://doc.rust-lang.org/std/io/trait.Write.html (Write trait on Rust std)

# v0.11.0-beta.2

- `Solver::set_custom_logic`
- more documentation improvements
- fixed some problems in code/doc formatting (internal)

# v0.11.0-beta.0

- slightly improved CVC4 support
- added support for Yices 2
- some (slight) documentation improvements
- fixed some problems in code/doc formatting (internal)

# v0.10.0

- switched to edition 2018
- removed a lot of the `Copy` requirements for parsers and input collections
  for `declare_fun` *etc*...
- various minor code embellishments

# v0.9.11

- (probably) fixed backend solvers being (sometimes) zombified when unwinding
- improved `check_sat_assuming` over iterators
- rustfmt!

# v0.9.10

- support `timeout`s
- `Solver` now implements `Write` ; this allows users to write custom commands
  directly
- separated `ValueParser` and `ModelParser` ; this fixes model parsing which
  wasn't making sense when parsing function definitions

# v0.9.9

- improved `SmtConf` to support `String` options and commands with options
- `Solver::path_tee` tees the solver to file given by path
- fixed/improved solver-level error handling

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