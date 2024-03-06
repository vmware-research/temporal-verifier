#!/bin/bash

# Copyright 2022-2023 VMware, Inc.
# SPDX-License-Identifier: BSD-2-Clause

## This script measures the time it takes to build temporal-verifier under various configurations.
##
## Run it from the root of the repository, like this:
##
##     ./tools/compile-times.sh
##
## You can also pass additional filenames on the command line to benchmark the scenario "how long
## does it take to rebuild after changing this file", as in:
##
##     ./tools/compile-times.sh fly/src/syntax.rs inference/src/basics.rs

set -e

function cargo_under_config() {
  CONFIG="$1"
  /usr/bin/time -p cargo build "$CONFIG" 2>&1 | tail -n 3 | head -n 1 | sed 's/^real /    /'
}

function build_after_touching() {
  CONFIG="$1"
  shift
  FILE="$1"
  shift

  echo "  building after touching $FILE:"
  touch "$FILE"
  cargo_under_config "$CONFIG"
}

function build_under_config() {
  CONFIG="$1"
  shift
  echo building with config "'$CONFIG'"

  echo -n '  cleaning...'
  cargo clean >/dev/null 2>&1
  echo ' clean.'

  echo '  building from scrach:'
  cargo_under_config "$CONFIG"

  echo '  building after touching all .rs files:'
  find . -iname '*.rs' -not -path './target/*' -exec touch {} \+
  cargo_under_config "$CONFIG"

  build_after_touching "$CONFIG" temporal-verifier/src/command.rs

  # loop over remaining arguments, if any
  until [ -z "$1" ]; do
    FILE="$1"
    shift

    build_after_touching "$CONFIG" "$FILE"
  done
}

build_under_config "" "$@"
build_under_config "--release" "$@"
