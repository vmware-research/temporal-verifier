# Temporal Verifier

[![CI](https://github.com/vmware-research/temporal-verifier/actions/workflows/build.yml/badge.svg)](https://github.com/vmware-research/temporal-verifier/actions/workflows/build.yml)

## Overview

An experimental framework for temporal verification based on
first-order linear-time temporal logic. Our goal is to express
transition systems in first-order logic and verify temporal
correctness properties, including safety and liveness.

## Try it out

Run `./tools/download-solvers.sh` to get compatible versions of the supported SMT solvers (Z3, CVC5, and CVC4).

```sh
cargo run -- verify temporal-verifier/examples/lockserver.fly

cargo run -- infer qalpha temporal-verifier/examples/lockserver.fly --quantifier "F node 2" --clause-size=3 --cubes=0

# invariant inference with qalpha
# note: this example takes several minutes to run
env RUST_LOG=info cargo run --release -- \
  infer qalpha temporal-verifier/examples/consensus_epr.fly --time \
  --custom-quant --sort quorum --sort node --sort value \
  --max-exist 1 --abort-unsafe --until-safe --minimal-smt \
  --extend-depth 1 --extend-width 10

# bounded model checking
cargo run -r -- set-check temporal-verifier/examples/consensus.fly \
  --bound node=2 --bound value=2 --bound quorum=2

## bounded model checking using a sat solver
cargo run -r -- sat-check temporal-verifier/examples/consensus.fly \
  --bound node=2 --bound value=2 --bound quorum=2 --depth=15
```

### Prerequisites

You'll need Rust (for example, through `rustup`) - stable and nightly should
both work. To get the right versions of the solvers run
`./tools/download-solvers.sh`, which are needed to run all the tests.

### Build & Run

1. `cargo build`
2. `cargo test` to run tests
3. `cargo run -- verify <file.fly>` will run the verifier on an input file

You can run `cargo bench` to run the performance benchmarks.

For debug logging, we use the
[env_logger](https://docs.rs/env_logger/latest/env_logger/) crate, which uses
the `RUST_LOG` environment variable to configure logging. For example, to get
info-level messages run with `env RUST_LOG=info cargo run -- ...`.

### API documentation

You can read the automatically generated rustdoc documentation by running:

```sh
cargo doc --document-private-items --no-deps --open
```

The code is split into several top-level crates, which are listed in the sidebar
of the documentation. `cargo doc` opens the alphabetically first crate, which
happens to be `bounded`, but you may want to start reading from the `fly` crate.
The overall organization of crates is the following:

There are three "core" crates:

* [smtlib](smtlib) low-level interface to the Z3 and CVC5 solvers
* [fly](fly) the core "fly" language and general tools
* [solver](solver) a solver interface that is based on fly's terms rather than
  s-expressions

On top of these tools we implement several features in independent crates:

* [verify](verify) prove safety using user-provided invariants
* [inference](inference) infer inductive invariants
* [bounded](bounded) a few implementations of bounded model checkers for safety problems
* [temporal-verifier](temporal-verifier) the command-line interface to all flyvy tools

### Performance benchmarking

The first step is to run `temporal-verifier infer` or `temporal-verifier verify`
with the `--time` option, which will give some coarse results on how much time
is spent in the solver vs. in the Rust code. If most time is spent in the
solver, these profiling methods won't provide too much insight (though in
principle if you use a build of Z3 or CVC5 with debug symbols `perf` would give
meaningful results, but interpreting them is another story).

Next, use `cargo flamegraph` (installed from
[GitHub](https://github.com/flamegraph-rs/flamegraph)): just use `cargo
flamegraph` in place of `cargo run --release` to run some command, then look at
the resulting `flamegraph.svg`. This shows where time is spent, organized by
call stack.

On Linux, you can use `perf` to get per-function statistics. Perf can do many,
many things, but here's a simple way to use it. First, run `perf record -s -g -F
500
--call-graph dwarf -- ./target/release/temporal-verifier ...` to generate a
`perf.data` file. To process it, you can use `perf report` to pull up an
interactive terminal UI, or run `perf script -F +pid,+time > test.perf` to
generate a file that can be uploaded to
[profiler.firefox.com](https://profiler.firefox.com) and explored with a nice
UI.

## Documentation

Run `cargo doc` to generate the low-level API documentation. Currently there
isn't much documentation for the language itself, but you can look at the
examples under `examples/`.

## Contributing

The temporal-verifier project team welcomes contributions from the community. Before you start working with temporal-verifier, please
read our [Developer Certificate of Origin](https://cla.vmware.com/dco). All contributions to this repository must be
signed as described on that page. Your signature certifies that you wrote the patch or have the right to pass it on
as an open-source patch. For more detailed information, refer to [CONTRIBUTING.md](CONTRIBUTING.md).

## License

Copyright 2022-2023 VMware, Inc.

SPDX-License-Identifier: BSD-2-Clause

See [NOTICE](NOTICE) and [LICENSE](LICENSE).
