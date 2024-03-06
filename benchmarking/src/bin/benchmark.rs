// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Run all of the examples as benchmarks and report the results in a table.

use std::{path::PathBuf, time::Duration};

use benchmarking::{
    qalpha::qalpha_benchmarks,
    report,
    run::{get_examples, BenchmarkConfig, BenchmarkMeasurement},
    time_bench::{compile_flyvy_bin, compile_time_bin, REPO_ROOT_PATH},
};
use clap::{Args, Parser};
use glob::Pattern;

#[derive(Args, Debug, Clone, PartialEq, Eq)]
struct QalphaParams {
    /// Glob pattern over benchmark names to run
    #[arg(short = 'F', long = "filter", default_value = "*")]
    name_glob: String,
    /// Output directory to store results
    #[arg(long)]
    output_dir: PathBuf,
    #[arg(long, default_value = "600s")]
    safety_time_limit: humantime::Duration,
    #[arg(long, default_value = "600s")]
    fixpoint_time_limit: humantime::Duration,
    #[arg(long, default_value = "600s")]
    scalability_time_limit: humantime::Duration,
}

#[derive(clap::Subcommand, Clone, Debug, PartialEq, Eq)]
enum Command {
    /// Run verification benchmarks with user-supplied invariants.
    Verify {
        /// Time limit for verifying each file.
        #[arg(long, default_value = "60s")]
        time_limit: humantime::Duration,
        /// Solver to use
        #[arg(long, default_value = "z3")]
        solver: String,
        #[arg(long)]
        /// Output results in JSON format
        json: bool,
    },
    /// Run invariant inference benchmarks with qalpha.
    Qalpha(#[command(flatten)] QalphaParams),
    /// Load and report a previously gathered set of results.
    Report {
        /// Directory to load from (recursively)
        dir: PathBuf,
    },
}

#[derive(clap::Parser, Debug)]
struct App {
    /// Command to run
    #[command(subcommand)]
    command: Command,
}

fn benchmark_verify(time_limit: Duration, solver: &str) -> Vec<BenchmarkMeasurement> {
    get_examples()
        .into_iter()
        .map(|file| {
            eprintln!(
                "verify {}",
                file.strip_prefix(REPO_ROOT_PATH()).unwrap().display()
            );
            BenchmarkMeasurement::run(
                BenchmarkConfig {
                    command: vec![String::from("verify")],
                    params: vec![format!("--solver={solver}")],
                    file,
                    time_limit,
                },
                None, /* rust_log */
                None, /* output_dir */
            )
        })
        .collect()
}

fn run_qalpha(params: &QalphaParams) -> Vec<BenchmarkMeasurement> {
    let name_glob = Pattern::new(&params.name_glob).expect("could not parse pattern");
    qalpha_benchmarks(
        params.safety_time_limit.into(),
        params.fixpoint_time_limit.into(),
        params.scalability_time_limit.into(),
    )
    .into_iter()
    .filter(|(name, _)| name_glob.matches_path(name))
    .map(|(file, config)| {
        eprintln!("qalpha {}", file.display());
        let result = BenchmarkMeasurement::run(
            config,
            Some("info".to_string()),
            Some(params.output_dir.join(file)),
        );
        eprintln!(
            "  took {:0.0}s{}",
            result.measurement.real_time.as_secs_f64(),
            if result.measurement.success {
                ""
            } else {
                " (failed)"
            }
        );
        result
    })
    .collect()
}

impl App {
    fn exec(&self) {
        // make sure `time` is available
        compile_time_bin();
        // make sure `temporal-verifier` is available
        compile_flyvy_bin();
        match &self.command {
            Command::Verify {
                time_limit,
                solver,
                json,
            } => {
                let results = benchmark_verify((*time_limit).into(), solver);
                if *json {
                    println!("{}", BenchmarkMeasurement::to_json(&results));
                } else {
                    BenchmarkMeasurement::print_table(results);
                }
            }
            Command::Qalpha(params) => {
                let _results = run_qalpha(params);
            }
            Command::Report { dir } => {
                let results = report::load_results(dir);
                BenchmarkMeasurement::print_table(results);
            }
        }
    }
}

fn main() {
    let app = App::parse();
    app.exec();
}
