// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Library for running and reporting benchmark measurements.

use std::{
    ffi::OsStr,
    fs::{self, File},
    io::Write,
    path::PathBuf,
    time::Duration,
};

use crate::{
    measurement::RunMeasurement,
    time_bench::{Time, REPO_ROOT_PATH},
};

use walkdir::WalkDir;

/// The setup for a benchmark
///
/// command + args form the arguments to temporal-verifier. These are split so
/// the configuration is output in a more structured manner; `command` is something
/// like `infer qalpha` while `args` has other configuration and quantifiers for
/// each sort, for example.
///
/// file is added to the end of the argument list and also becomes a
/// separate column in the results.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct BenchmarkConfig {
    /// Command gives the initial arguments to temporal-verifier (eg, "verify"
    /// or "infer qalpha").
    pub command: Vec<String>,
    /// Params are any additional arguments to the subcommand.
    pub params: Vec<String>,
    /// File is the final argument
    pub file: PathBuf,
    /// Time limit before killing benchmark
    pub time_limit: Duration,
}

impl BenchmarkConfig {
    fn args(&self) -> Vec<String> {
        let mut args = self.command.clone();
        args.extend(self.params.iter().cloned());
        args.push(self.file.to_str().unwrap().to_string());
        args
    }
}

/// A benchmark configuration and its resulting measurement.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct BenchmarkMeasurement {
    /// The configuration used to run the benchmark.
    pub config: BenchmarkConfig,
    /// The measurements (time, success, etc) from the run.
    pub measurement: RunMeasurement,
}

impl BenchmarkMeasurement {
    /// Run flyvy on a single benchmark, isolated to its own process.
    pub fn run(
        config: BenchmarkConfig,
        rust_log: Option<String>,
        output_dir: Option<PathBuf>,
    ) -> Self {
        let mut timer = flyvy_timer();
        timer.timeout(config.time_limit);
        timer.args(config.args());
        timer.rust_log = rust_log.unwrap_or("".to_string());
        if let Some(ref output_dir) = output_dir {
            timer.output_dir(output_dir);
            fs::create_dir_all(output_dir).expect("could not create output directory");
            let mut f = File::create(output_dir.join("command"))
                .expect("could not create file for command");
            writeln!(&mut f, "{}", timer.cmdline()).expect("could not write command");
            let mut f = File::create(output_dir.join("config.json")).unwrap();
            serde_json::to_writer(&mut f, &config).expect("could not serialize config");
            _ = writeln!(&mut f);
        }
        let measurement = timer.run().expect("error getting timing");
        if let Some(ref output_dir) = output_dir {
            let mut f = File::create(output_dir.join("measurement.json"))
                .expect("could not create file for measurement");
            serde_json::to_writer(&mut f, &measurement).expect("could not serialize measurement");
            _ = writeln!(&mut f);
        }
        BenchmarkMeasurement {
            config,
            measurement,
        }
    }

    /// Convert a list of results to newline-separated JSON.
    pub fn to_json(results: &[Self]) -> String {
        results
            .iter()
            .map(|r| serde_json::to_string(r).expect("could not serialize `RunResult`"))
            .collect::<Vec<_>>()
            .join("\n")
    }
}

/// Create an instance of Time that runs temporal-verifier
fn flyvy_timer() -> Time {
    Time::new(REPO_ROOT_PATH().join("target/release/temporal-verifier"))
}

/// Get all the .fly examples from `temporal-verifier/examples`.
pub fn get_examples() -> Vec<PathBuf> {
    let root = REPO_ROOT_PATH();
    let examples_dir = root.join("temporal-verifier/examples");
    WalkDir::new(examples_dir)
        .sort_by_file_name()
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().is_file() && e.path().extension() == Some(OsStr::new("fly")))
        .map(|e| e.into_path())
        .collect()
}
