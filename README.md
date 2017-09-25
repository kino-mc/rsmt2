# `rsmt2`

| linux | windows |     |     |
|:-----:|:-------:|:---:|:---:|
| [![Build Status](https://travis-ci.org/kino-mc/rsmt2.svg?branch=master)](https://travis-ci.org/kino-mc/rsmt2) | [![Build status](https://ci.appveyor.com/api/projects/status/db247pe2jp9uo9cs?svg=true)](https://ci.appveyor.com/project/AdrienChampion/rsmt2) | [![Latest Version](https://img.shields.io/crates/v/rsmt2.svg)](https://crates.io/crates/rsmt2) | [![codecov](https://codecov.io/gh/kino-mc/rsmt2/branch/master/graph/badge.svg)](https://codecov.io/gh/kino-mc/rsmt2)

A generic library to interact with SMT-LIB 2 compliant solvers running in a separate system process, such as Z3 and CVC4.

[Crate.io documentation.][doc]


If you use this library consider contacting us on the [repository](https://github.com/kino-mc/rsmt2) so that we can add your project to the readme.

See [`CHANGES.md`](https://github.com/kino-mc/rsmt2/blob/master/README.md) for
the list of changes.


# Missing features

- support for solvers other than z3
- `get-proof`


# Known projects using `rsmt2`

- [kinō][kino], a model-checker for transition systems
- [hoice][hoice], a machine-learning-based predicate synthesizer for horn clauses

# License

MIT/Apache-2.0

[doc]: https://docs.rs/rsmt2 (Documentation)
[kino]: https://github.com/kino-mc/kino (kino on github)
[hoice]: https://github.com/hopv/hoice (hoice on github)