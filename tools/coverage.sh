#!/usr/bin/env bash

# Copyright 2022-2023 VMware, Inc.
# SPDX-License-Identifier: BSD-2-Clause

## Gather code coverage from tests.
##
## Uses cargo-llvm-cov. Install with `cargo install cargo-llvm-cov`, or follow
## https://github.com/taiki-e/cargo-llvm-cov#installation.
##
## We use this setup rather than simply running `cargo llvm-cov` as-is because
## the tests invoke the `temporal-verifier` binary, and much of the coverage
## comes from those calls. The code below compiles the binary itself with
## instrumentation built-in, then runs the tests, and finally merges all of the
## gathered coverage reports.
##
## Generates lcov.info and then uses any additional arguments to the script to
## produce another report. If no arguments are passed, defaults to `--html
## --open`.

set -e

if ! which cargo-llvm-cov >/dev/null 2>&1; then
  echo "cargo llvm-cov not found" 1>&2
  echo "see https://github.com/taiki-e/cargo-llvm-cov#installation" 1>&2
  exit 1
fi

# non-constant source
# shellcheck disable=SC1090
source <(cargo llvm-cov show-env --export-prefix)
cargo llvm-cov clean --workspace
cargo test
if [ $# -gt 0 ]; then
  cargo llvm-cov report "$@"
fi
cargo llvm-cov report --lcov --output-path lcov.info
