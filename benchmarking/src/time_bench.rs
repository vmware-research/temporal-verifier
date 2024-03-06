// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Tools for running a benchmark and gathering performance statistics like
//! runtime, CPU time, and memory usage. Also allows killing the benchmark with
//! a timeout.

use std::{
    env,
    ffi::{OsStr, OsString},
    fs::File,
    io,
    os::fd::{AsRawFd, IntoRawFd},
    path::{Path, PathBuf},
    process::{Command, ExitCode, Stdio},
    sync::{Arc, Mutex},
    thread,
    time::{Duration, Instant},
};

use fork::Fork;
use nix::{
    errno::Errno,
    fcntl::{self, OFlag},
    sys::{
        resource::{getrusage, Usage, UsageWho},
        signal::{killpg, Signal},
        stat::Mode,
        time::TimeVal,
        wait::{waitpid, WaitStatus},
    },
    unistd::{dup2, getpgid, setsid, Pid},
};
use process_sync::{SharedCondvar, SharedMutex};

use crate::measurement::RunMeasurement;

/// The `time` utility runs a benchmark, optionally kills it after a timeout,
/// and gathers resource usage statistics.
///
/// It is implemented as a separate binary to enable appropriate process
/// isolation (in particular to run `getrusage` and get statistics for a single
/// benchmark). It is more commonly used programmatically, with the library that
/// wraps the binary in a nice Rust interface.
#[derive(clap::Parser, Debug)]
pub struct Time {
    /// Kill process after this much time
    #[arg(long, short)]
    pub time_limit: Option<humantime::Duration>,
    /// Output in JSON rather than a human-readable format
    #[arg(long)]
    pub json: bool,
    /// Directory to store stdout and stderr in
    #[arg(long)]
    pub output_dir: Option<PathBuf>,
    /// RUST_LOG level to set in child process
    #[arg(long, default_value = "")]
    pub rust_log: String,
    /// Program to run
    pub prog: OsString,
    /// Arguments to pass
    pub args: Vec<OsString>,
}

/// Get the temporal-verifier root path.
/// TODO: Only works when using a binary compiled locally. Will need to fix when
/// distributing a precompiled binary.
#[allow(non_snake_case)]
pub fn REPO_ROOT_PATH() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("could not get parent directory of benchmarking package")
}

fn time_bin() -> PathBuf {
    let target = REPO_ROOT_PATH().join("target");
    let release = target.join("release/time");
    if release.exists() {
        return release;
    }
    let debug = target.join("debug/time");
    if debug.exists() {
        return debug;
    }
    panic!("time binary not available - try cargo build --bin time")
}

/// Run cargo and print a warning if it fails
fn run_cargo<S, I>(args: I)
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let args = args
        .into_iter()
        .map(|s| s.as_ref().to_owned())
        .collect::<Vec<_>>();
    let status = Command::new("cargo")
        .arg("--quiet")
        .args(&args)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::inherit())
        .current_dir(REPO_ROOT_PATH())
        .status();
    match status {
        Ok(status) => {
            if !status.success() {
                eprintln!(
                    "cargo {} failed",
                    args.join(OsStr::new(" ")).to_string_lossy()
                );
            }
        }
        Err(err) => {
            eprintln!("could not run cargo: {err}");
        }
    }
}

/// Build the `time` binary, which is an implicit dependency of benchmarks.
pub fn compile_time_bin() {
    run_cargo(["build", "--release", "--bin", "time"]);
}

/// Compile the `temporal-verifier` binary, which is run by the benchmarks.
pub fn compile_flyvy_bin() {
    run_cargo(["build", "--release", "--bin", "temporal-verifier"]);
}

#[derive(Debug, Clone)]
struct RawRunMeasurement {
    real_time: Duration,
    usage: Usage,
    self_usage: Usage,
    timed_out: bool,
    status: Option<i32>,
}

fn time_val_to_duration(time: TimeVal) -> Duration {
    Duration::from_secs(time.tv_sec() as u64) + Duration::from_micros(time.tv_usec() as u64)
}

impl RawRunMeasurement {
    fn max_rss_bytes(&self) -> i64 {
        if cfg!(target_os = "macos") {
            // macOS reports maxrss in bytes
            self.usage.max_rss()
        } else {
            // on Linux maxrss is in KB
            self.usage.max_rss() * 1024
        }
    }

    fn into_measurement(self) -> RunMeasurement {
        RunMeasurement {
            real_time: self.real_time,
            user_time: time_val_to_duration(self.usage.user_time()),
            sys_time: time_val_to_duration(self.usage.system_time()),
            self_user_time: time_val_to_duration(self.self_usage.user_time()),
            max_mem_bytes: self.max_rss_bytes() as usize,
            timed_out: self.timed_out,
            success: self.status == Some(0),
        }
    }
}

impl Time {
    fn get_child_measurements(&self, child: i32) -> Result<RawRunMeasurement, io::Error> {
        let child = Pid::from_raw(child);
        let start = Instant::now();
        let timeout = Arc::new(Mutex::new(false));
        if let Some(limit) = &self.time_limit {
            let limit: Duration = (*limit).into();
            let pgid = getpgid(Some(child)).expect("could not get child pgid");
            let timeout = timeout.clone();
            thread::spawn(move || {
                thread::sleep(limit);
                // hold a lock on the timeout flag until we determine whether a
                // timeout really occurred or not
                let mut timeout = timeout.lock().unwrap();
                let r = killpg(pgid, Signal::SIGTERM);
                if let Err(err) = r {
                    // this happens when the child no longer exists
                    if err == Errno::EPERM {
                        // exit without setting timeout flag
                        return;
                    }
                    eprintln!("could not send SIGTERM: {err}");
                }
                // now set the timeout flag because the timer really did expire
                *timeout = true;
                drop(timeout);
                thread::sleep(Duration::from_secs(1));
                eprintln!("sending SIGKILL");
                _ = killpg(pgid, Signal::SIGKILL);
            });
        }

        let wstatus = waitpid(Some(child), None)?;
        let status = match wstatus {
            WaitStatus::Exited(_, status) => Some(status),
            _ => None,
        };
        let real_time = start.elapsed();
        let timed_out = *timeout.lock().unwrap();
        let usage = getrusage(UsageWho::RUSAGE_CHILDREN)?;
        let self_usage = getrusage(UsageWho::RUSAGE_SELF)?;
        let measurement = RawRunMeasurement {
            real_time,
            usage,
            self_usage,
            timed_out,
            status,
        };
        Ok(measurement)
    }

    /// Run `time` with the arguments in `self`. This uses `fork` and `exec`
    /// directly and is thus only intended for running from the `time` binary,
    /// not from user code.
    pub fn exec(&self) -> Result<ExitCode, io::Error> {
        let (mut lock, mut cvar) = (SharedMutex::new().unwrap(), SharedCondvar::new().unwrap());
        match fork::fork() {
            Ok(Fork::Parent(child)) => {
                cvar.wait(&mut lock).unwrap();
                let measurements = self.get_child_measurements(child)?;
                let parsed = measurements.clone().into_measurement();
                if self.json {
                    println!("{}", parsed.to_json());
                } else {
                    parsed.print();
                }
                // timed_out is true if and only if the timeout thread triggers
                // (even if this happens after the child exits)
                if measurements.timed_out {
                    // to match behavior of `timeout(1)`
                    return Ok(ExitCode::from(124u8));
                }
                if let Some(code) = measurements.status {
                    return Ok(ExitCode::from(code as u8));
                }
                Ok(ExitCode::SUCCESS)
            }
            Ok(Fork::Child) => {
                _ = setsid();
                cvar.notify_one().unwrap();
                match &self.output_dir {
                    Some(dir) => {
                        let stdout = File::create(dir.join("stdout"))
                            .expect("could not create stdout file")
                            .into_raw_fd();
                        dup2(stdout, io::stdout().as_raw_fd())
                            .expect("could not replace stdout with file");
                        let stderr = File::create(dir.join("stderr"))
                            .expect("could not create stderr file")
                            .into_raw_fd();
                        dup2(stderr, io::stderr().as_raw_fd())
                            .expect("could not replace stderr with file");
                    }
                    None => {
                        // suppress stdout (but not stderr)
                        let null = fcntl::open("/dev/null", OFlag::O_WRONLY, Mode::empty())
                            .expect("could not get /dev/null");
                        dup2(null, io::stdout().as_raw_fd())
                            .expect("could not replace stdout with null");
                    }
                }
                if !self.rust_log.is_empty() {
                    env::set_var("RUST_LOG", self.rust_log.clone());
                }
                let err = exec::Command::new(&self.prog).args(&self.args).exec();
                eprintln!("exec failed: {err}");
                // mimic `timeout(1)` (although it distinguishes the command
                // being found vs not found)
                Ok(ExitCode::from(126))
            }
            Err(err) => {
                eprintln!("fork failed: {err}");
                // mimic `timeout(1)`
                Ok(ExitCode::from(125))
            }
        }
    }

    /// Create a new timing config for library use.
    #[allow(clippy::new_without_default)]
    pub fn new<S: AsRef<OsStr>>(prog: S) -> Self {
        Self {
            time_limit: None,
            json: true,
            output_dir: None,
            rust_log: "".to_string(),
            prog: prog.as_ref().to_owned(),
            args: vec![],
        }
    }

    /// Set the time limit of `self`.
    pub fn timeout(&mut self, limit: Duration) -> &mut Self {
        self.time_limit = Some(limit.into());
        self
    }

    /// Set the output directory of `self`.
    pub fn output_dir<P: AsRef<Path>>(&mut self, dir: P) -> &mut Self {
        self.output_dir = Some(dir.as_ref().to_owned());
        self
    }

    /// Set the RUST_LOG for the child in `self`.
    pub fn rust_log<S: AsRef<str>>(&mut self, level: S) -> &mut Self {
        self.rust_log = level.as_ref().to_owned();
        self
    }

    /// Append an argument to `self`.
    pub fn arg<S: AsRef<OsStr>>(&mut self, arg: S) -> &mut Self {
        self.args.push(arg.as_ref().to_owned());
        self
    }

    /// Append multiple arguments to `self`.
    pub fn args<I, S>(&mut self, args: I) -> &mut Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<OsStr>,
    {
        self.args
            .extend(args.into_iter().map(|s| s.as_ref().to_owned()));
        self
    }

    /// Get the command line to be run for debugging purposes (for example, to
    /// run manually).
    pub fn cmdline(&self) -> String {
        let mut cmdline: Vec<String> = vec![self.prog.to_string_lossy().to_string()];
        for arg in &self.args {
            let arg = arg.to_string_lossy();
            if arg.contains([' ', '"']) {
                cmdline.push(format!("\"{}\"", arg.replace('"', "\\\"")));
            } else {
                cmdline.push(arg.to_string())
            }
        }
        cmdline.join(" ")
    }

    /// Run a compiled `time` binary using the arguments in `self`.
    ///
    /// This must use the binary rather than running `exec()` directly in order
    /// to isolate resource usage measurement.
    pub fn run(&self) -> Result<RunMeasurement, io::Error> {
        let mut cmd = Command::new(time_bin());
        if let Some(limit) = &self.time_limit {
            cmd.arg("--time-limit");
            cmd.arg(format!("{}s", limit.as_secs_f64()));
        }
        if self.json {
            cmd.arg("--json");
        }
        if let Some(output_dir) = self.output_dir.as_ref() {
            cmd.arg("--output-dir");
            cmd.arg(output_dir);
        }
        cmd.arg("--rust-log");
        cmd.arg(&self.rust_log);

        cmd.arg("--");
        cmd.arg(&self.prog);
        cmd.args(&self.args);
        let output = cmd.output()?;
        let output = std::str::from_utf8(&output.stdout).expect("non utf-8 output");
        match RunMeasurement::from_json(output) {
            Ok(r) => Ok(r),
            Err(err) => {
                eprintln!("{output}");
                panic!("could not parse JSON from time: {err}")
            }
        }
    }
}
