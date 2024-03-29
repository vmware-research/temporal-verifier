#!/bin/bash

# Copyright 2022-2023 VMware, Inc.
# SPDX-License-Identifier: BSD-2-Clause

## This script runs the checks that we use in CI.
##
## When run locally without arguments, command are run with less verbose output.
## In CI we pass the --ci flag to produce verbose output from the build and test
## steps.

set -eu

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"

cd "$SCRIPT_DIR/.."

blue=$(tput setaf 4 2>/dev/null || printf "")
red=$(tput setaf 1 2>/dev/null || printf "")
reset=$(tput sgr0 2>/dev/null || printf "")

info() {
  echo -e "${blue}$1${reset}"
}
error() {
  echo -e "${red}$1${reset}"
}

usage() {
  echo "$0 [--ci] [--fast]"
  echo "  --ci    add verbosity and some commands for GitHub actions"
  echo "  --fast  run fast checks (skips building and testig)"
}

ci=""
fast=""
while [[ $# -gt 0 ]]; do
  case "$1" in
  --ci)
    shift
    ci=true
    ;;
  --fast)
    shift
    fast=true
    ;;
  -h | -help | --help)
    usage
    exit 0
    ;;
  *)
    echo "unknown option/argument" 1>&2
    exit 1
    ;;
  esac
done

start_group() {
  if [ "$ci" = true ]; then
    echo "::group::$1"
  fi
  info "$1"
}

end_group() {
  if [ "$ci" = true ]; then
    echo "::endgroup::"
  fi
}

if [ "$fast" != true ]; then
  start_group "cargo build"
  params=(--tests)
  if [ "$ci" = true ]; then
    cargo build --verbose "${params[@]}"
  else
    cargo build --quiet "${params[@]}"
  fi
  end_group
fi

if [ "$fast" != true ]; then
  start_group "cargo test"
  params1=(--lib --bins --tests --examples -- --include-ignored)
  params2=(--benches --)
  if [ "$ci" = true ]; then
    cargo test --verbose "${params1[@]}" --nocapture
    cargo test --verbose "${params2[@]}" --nocapture
  else
    cargo test --quiet "${params1[@]}"
    cargo test --quiet "${params2[@]}"
  fi
  end_group
fi

info "cargo fmt --check"
if [ "$ci" = true ]; then
  cargo fmt --check
else
  ## locally we check but also apply the diff

  # run the usual check, print a diff if needed, and remember if it succeeded
  if cargo fmt --check; then
    fmt_good=true
  else
    fmt_good=false
  fi
  # actually apply the diff locally
  cargo fmt
  if [ "$fmt_good" = false ]; then
    error "cargo fmt made some changes"
    exit 1
  fi
fi

start_group "cargo clippy"
params=(--tests -- --no-deps -D clippy::all)
if [ "$ci" = true ]; then
  cargo clippy "${params[@]}"
else
  cargo clippy --quiet "${params[@]}"
fi
end_group

start_group "cargo doc"
params=(--document-private-items --no-deps)
if [ "$ci" = true ]; then
  cargo doc "${params[@]}"
else
  cargo doc --quiet "${params[@]}"
fi
end_group

start_group "project-specific lints"
if grep -wr --include '*.rs' --exclude ouritertools.rs multi_cartesian_product; then
  error "found some occurrences of multi_cartesian_product; use multi_cartesian_product_fixed to handle empty iterators correctly"
  exit 1
fi
end_group
