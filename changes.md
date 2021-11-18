# v0.14.1

- properly `wait` for child solver process, [#29](https://github.com/kino-mc/rsmt2/issues/29)

# v0.14.0

- `Solver::get_interpolant` now mature enough for actual use (examples in doc)
- `()` now implements all parser traits but `ProofParser` (generates `&str` or `String`)
- overall improvements documentation-wise, including more examples

# v0.13.1

- added *named assert* function on `Solver`s
    - `Solver::named_assert_act_with`: named + actlit + print info
    - `Solver::named_assert_with`: named + print info
    - `Solver::named_assert`: named
- simplified most `Solver` function signatures
    - take ownership over expressions, symbols and sorts (previously took references)

        still accepts refs since `T: Sym2Smt<Info>` ⇒ `&T: Sym2Smt<Info>`, same for `Expr2Smt` and
        `Sort2Smt`.
    - `Solver` functions taking collections (iterators) now abstract over what they expect the items
        to be. Previously, they had to be (constrained) pairs or triplets. They now expect some type
        implementing the relevant trait for the information they expect (`SymAndSort` for instance).
        These traits are implemented for the pairs/triplets from previous versions: this new
        workflow should not break existing code.
    - **[breaking]** revamp of `declare_datatypes`, see documentation.

        Relevant traits are `AdtDecl`, `AdtVariant` and `AdtVariantField`.

## Breaking Changes

- Use of `declare_datatypes` has changed significantly, will most likely break everything. Refer to
    the documentation for details, sorry.

# v0.13.0

- named expression
    - added `NamedExpr<Sym, Expr>` which wraps an expression and a symbol and encodes a named expression
    - added `into_named` and `as_named` methods on `Expr2Smt` trait for easy expression naming
    - added `into_name_for` and `as_name_for` methods on `Sym2Smt`
- unsat cores now working (best used with `NamedExpr` to name expressions)
    - relies on the `ParseSym` trait to parse symbols from the core
- interpolants (`get-interpolant`) now supported
    - only Z3 supports this
    - `SmtConf` produces an error if interpolant production is activated on a non-Z3 solver
    - uses `Sym2Smt`
    - best used with `NamedExpr` to name expressions
- `assert`-like functions on `Solver` no longer require the expression to be a reference
    - goes with `Expr2Smt<Info>` being auto-impl-ed for all `T: Expr2Smt<Info>`
- `Actlit` now implies `Sym2Smt`
- added `actlit::CondExpr`, which wraps an `Actlit` and a user expression; allows to use `Actlit`s
  in normal `check-sat` commands
- `SmtConf` now has `set_...` functions for model/unsat core/... production

# v0.12.0

- adapted parser for Z3's new `get-model` output, which does not use the `model` keyword

# v0.11.0

- a lot of documentation fixes/improvements
- asynchronous check-sat-s, see `asynch` module and `Solver::async_check_sat_or_unk`
- the commands to run each solver can now be passed through environment variables, see
    - the `conf` module, and
    - the `<solver>_or_env` functions on `SmtConf`.

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