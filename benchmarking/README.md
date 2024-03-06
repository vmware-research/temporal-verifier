# Run flyvy benchmarks over examples

The `benchmark` binary implements configuration for running benchmark suites
over the examples in `temporal-verifier/examples` and recording output and
timing results. Use `--help` (including with each subcommand) to get info on
parameters.

## qalpha invariant inference

Run `temporal-verifier infer qalpha` with hand-written configuration per
example. Records the full output of each run, as well as timing info. To
configure this benchmark edit [qalpha.rs](src/qalpha.rs).

```sh
cargo run --bin benchmark -- qalpha --output-dir qalpha-results
```

## Verification

Run `temporal-verifier verify` over all the examples.

```sh
cargo run --bin benchmark -- verify --time-limit 60s
```
