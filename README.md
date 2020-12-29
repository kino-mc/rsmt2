![crates.io](https://img.shields.io/crates/v/hashconsing.svg)
![Documentation](https://docs.rs/hashconsing/badge.svg)
![ci](https://github.com/AdrienChampion/hashconsing/workflows/ci/badge.svg)

# `rsmt2`

A generic library to interact with SMT-LIB 2 compliant solvers running in a separate system process,
such as [Z3][z3] and [CVC4][cvc4].


If you use this library consider contacting us on the [repository](https://github.com/kino-mc/rsmt2)
so that we can add your project to the readme.

See [`changes.md`](https://github.com/kino-mc/rsmt2/blob/master/README.md) for the list of changes.


# Future features (if requested)

- support for more solvers
- `get-proof`


# Known projects using `rsmt2`

- [kinō][kino], a model-checker for transition systems (abandoned)
- [hoice][hoice], a machine-learning-based predicate synthesizer for horn clauses

# License

MIT/Apache-2.0

[kino]: https://github.com/kino-mc/kino (kino on github)
[hoice]: https://github.com/hopv/hoice (hoice on github)
[z3]: https://github.com/Z3Prover/z3 (z3 on github)
[cvc4]: https://github.com/CVC4/CVC4 (cvc4 on github)