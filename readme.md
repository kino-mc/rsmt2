![crates.io](https://img.shields.io/crates/v/rsmt2.svg)
![Documentation](https://docs.rs/rsmt2/badge.svg)
![CI](https://github.com/kino-mc/rsmt2/workflows/CI/badge.svg)

# `rsmt2`

A generic library to interact with SMT-LIB 2 compliant solvers running in a separate system process,
such as [z3][z3] and [CVC4][cvc4].


If you use this library consider contacting us on the [repository](https://github.com/kino-mc/rsmt2)
so that we can add your project to the readme.

See [`changes.md`](https://github.com/kino-mc/rsmt2/blob/master/README.md) for the list of changes.


# Features

- [x] support main solvers ([z3][z3], [CVC4][cvc4], [Yices 2][yices2])
- [x] all basic declaration/definition/assertion/model/values commands
- [x] `check-sat-assuming`, with dedicated [actlit API]
- [x] the commands to run each solver can be passed through environment variables, see the `conf`
  module
- [ ] [alt-ergo][AE]
- [ ] `get-proof` command


# Known projects using `rsmt2`

- [kinō][kino], a model-checker for transition systems (abandoned)
- [hoice][hoice], a machine-learning-based predicate synthesizer for horn clauses

# License

MIT/Apache-2.0

[kino]: https://github.com/kino-mc/kino (kino on github)
[hoice]: https://github.com/hopv/hoice (hoice on github)
[z3]: https://github.com/z3Prover/z3 (z3 on github)
[cvc4]: https://github.com/CVC4/CVC4 (CVC4 on github)
[yices2]: https://yices.csl.sri.com/ (Yices 2 official)
[AE]: http://alt-ergo.lri.fr/ (Alt-Ergo official)
[actlit API]: https://docs.rs/rsmt2/latest/rsmt2/actlit/index.html (Actlit API on docs.rs)