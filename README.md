# Temporal Verifier

## Overview

An experimental framework for temporal verification based on
first-order linear-time temporal logic. Our goal is to express
transition systems in first-order logic and verify temporal
correctness properties, including safety and liveness.

## Try it out

`cargo run -- examples/fail/basic.fly`

### Prerequisites

You'll need Rust (for example, through `rustup`) and a recent version of [Z3](https://github.com/Z3Prover/z3).

### Build & Run

1. `cargo build`
2. `cargo test` to run tests
3. `cargo run -- <file.fly>` will run the verifier on an input file

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

Copyright 2022 VMware, Inc.

SPDX-License-Identifier: BSD-2-Clause

See [NOTICE](NOTICE) and [LICENSE](LICENSE).
