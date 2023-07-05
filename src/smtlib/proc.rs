// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Manage a running SMT process.
//!
//! This is a low-level generic API for SMT-LIB solvers; the solver-specific
//! parts are captured by the [`SolverCmd`] passed to launch the solver and in
//! the code that parses models returned by [`SmtProc::check_sat`].

use crate::smtlib::sexp;
use nix::{errno::Errno, sys::signal, unistd::Pid};
use std::hash::{Hash, Hasher};
use std::{
    collections::hash_map::DefaultHasher,
    ffi::{OsStr, OsString},
    fs::OpenOptions,
    io::{self, BufRead, BufReader, ErrorKind, Write},
    path::{Path, PathBuf},
    process::{Child, ChildStdin, ChildStdout, Command, Stdio},
    sync::{Arc, Mutex},
};
use thiserror::Error;

use std::os::unix::process::ExitStatusExt;

use super::sexp::{app, atom_s, sexp_l, Sexp};

#[derive(Debug)]
struct Tee {
    dir: PathBuf,
    contents: Vec<Sexp>,
}

fn calculate_hash<T: Hash>(v: T) -> String {
    let mut hash_state = DefaultHasher::new();
    v.hash(&mut hash_state);
    let h = hash_state.finish();
    return format!("{:016x}", h)[..8].to_string();
}

impl Tee {
    fn new<P: AsRef<Path>>(dir: P) -> Self {
        Self {
            dir: dir.as_ref().to_path_buf(),
            contents: vec![],
        }
    }

    fn append(&mut self, s: Sexp) {
        self.contents.push(s)
    }

    /// Save the SMT2 input currently sent to the solver to a file based on
    /// content hash. Returns the saved file name.
    fn save(&self) -> io::Result<PathBuf> {
        let contents = self
            .contents
            .iter()
            .map(|s| {
                if let Sexp::Comment(c) = s {
                    #[allow(clippy::comparison_to_empty)]
                    if c == "" {
                        return "".to_string();
                    }
                    return format!(";; {c}");
                }
                // TODO: this should be pretty-printed
                s.to_string()
            })
            .collect::<Vec<_>>()
            .join("\n");
        let hash = calculate_hash(&contents);
        let fname = PathBuf::from(format!("query-{hash}.smt2"));
        let dest = self.dir.join(&fname);
        let mut f = OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(dest)?;
        write!(&mut f, "{contents}")?;
        Ok(fname)
    }
}

/// SmtProc wraps an instance of a solver process.
#[derive(Debug)]
pub struct SmtProc {
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
    tee: Option<Tee>,
    // signal to SmtPids that this process has terminated (so we don't try to
    // kill the process long afterward when the pid might have been reused)
    terminated: Arc<Mutex<bool>>,
}

/// A handle to the SMT process for cancelling an in-progress check.
#[derive(Clone)]
pub struct SmtPid {
    pid: Pid,
    terminated: Arc<Mutex<bool>>,
}

/// SatResp is a solver's response to a `(check-sat)` or similar command.
///
/// For unknown it also returns the reason the solver provides.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SatResp {
    /// The query is satisfiable.
    Sat,
    /// The query is unsatisfiable (and thus negated assertions are valid).
    Unsat,
    /// Unknown whether the query is sat or unsat. The reason is the one given
    /// by (get-info :reason-unknown).
    ///
    /// This can happen due to a timeout or limitations of quantifier instantiation
    /// heuristics, for example.
    Unknown(String),
}

#[derive(Error, Debug)]
/// An error from trying to call the solver
///
/// NOTE: this is still highly incomplete and some errors actually result in a
/// panic.
pub enum SolverError {
    /// I/O went wrong
    #[error("some io went wrong: {0}")]
    Io(#[from] io::Error),
    /// Solver died for some reason
    #[error("solver returned an error:\n{0}")]
    UnexpectedClose(String),
    /// Solver killed specifically by SIGKILL signal
    #[error("solver was killed")]
    Killed,
}

type Result<T> = std::result::Result<T, SolverError>;

/// The full invocation of a solver binary.
#[derive(Debug, Clone)]
pub struct SolverCmd {
    /// Binary to launch
    pub cmd: String,
    /// Arguments to pass
    pub args: Vec<String>,
    /// SMT options to send on startup
    pub options: Vec<(String, String)>,
}

impl SolverCmd {
    fn args<I, S>(&mut self, args: I)
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        self.args
            .extend(args.into_iter().map(|s| s.as_ref().to_string()));
    }

    /// Set an option.
    pub fn option<S: AsRef<str>>(&mut self, name: &str, val: S) {
        self.options
            .push((name.to_string(), val.as_ref().to_string()));
    }

    fn cmdline(&self) -> String {
        #[allow(clippy::useless_format)]
        let args: Vec<_> = self
            .args
            .iter()
            .map(|a| {
                if a.contains(' ') {
                    format!("\"{a}\"")
                } else {
                    format!("{a}")
                }
            })
            .collect();
        format!("{} {}", &self.cmd, args.join(" "))
    }
}

/// Builder for creating a Z3 [`SolverCmd`].
#[derive(Debug, Clone)]
pub struct Z3Conf(SolverCmd);

impl Z3Conf {
    /// Create a Z3Conf with some default options. Uses `cmd` as the path to Z3.
    pub fn new(cmd: &str) -> Self {
        let mut cmd = SolverCmd {
            cmd: cmd.to_string(),
            args: vec![],
            options: vec![],
        };
        cmd.args(["-in", "-smt2"]);
        cmd.option("model.completion", "true");
        let mut conf = Self(cmd);
        conf.timeout_ms(Some(30000 * 100));
        conf
    }

    /// Enable model compaction
    pub fn model_compact(&mut self) {
        self.0.option("model.compact", "true");
    }

    /// Set the SMT timeout option
    pub fn timeout_ms(&mut self, ms: Option<usize>) {
        // this is the default Z3 timeout
        let ms = ms.unwrap_or(4294967295);
        self.0.option("timeout", format!("{ms}"));
    }

    /// Get access to the raw options of the solver.
    pub fn options(&mut self) -> &mut SolverCmd {
        &mut self.0
    }

    /// Get the final command to run the solver.
    pub fn done(self) -> SolverCmd {
        self.0
    }
}

/// Builder for a CVC4 or CVC5 [`SolverCmd`].
#[derive(Debug, Clone)]
pub struct CvcConf {
    version5: bool,
    cmd: SolverCmd,
}

impl CvcConf {
    fn new_cvc(cmd: &str, version5: bool) -> Self {
        let mut cmd = SolverCmd {
            cmd: cmd.to_string(),
            args: vec![],
            options: vec![],
        };
        // for CVC4, --lang smt2 is needed when using stdin, but when run on a
        // file with a .smt2 extension it will automatically use the right input
        // format.
        cmd.args(vec!["-q", "--lang", "smt2"]);
        cmd.option("interactive", "false");
        cmd.option("incremental", "true");
        cmd.option("seed", "1");
        Self { version5, cmd }
    }

    /// Create a new CVC4 builder with some default options.
    pub fn new_cvc4(cmd: &str) -> Self {
        Self::new_cvc(cmd, /*version5*/ false)
    }

    /// Create a new CVC5 builder with some default options.
    pub fn new_cvc5(cmd: &str) -> Self {
        Self::new_cvc(cmd, /*version5*/ true)
    }

    /// Enable finite model finding with mbqi.
    pub fn finite_models(&mut self) {
        self.cmd.option("finite-model-find", "true");
        if self.version5 {
            self.cmd.option("mbqi", "true");
            self.cmd.option("fmf-mbqi", "fmc")
        } else {
            self.cmd.option("mbqi", "fmc");
        }
    }

    /// Enable interleaving enumerative instantiation with other techniques.
    pub fn interleave_enumerative_instantiation(&mut self) {
        if self.version5 {
            self.cmd.option("enum-inst-interleave", "true");
        } else {
            self.cmd.option("fs-interleave", "true");
        }
    }

    /// Set a per-query time limit. None sets no time limit.
    pub fn timeout_ms(&mut self, ms: Option<usize>) {
        let ms = ms.unwrap_or(0);
        self.cmd.option("tlimit-per", format!("{ms}"));
    }

    /// Get access to the raw options of the solver.
    pub fn options(&mut self) -> &mut SolverCmd {
        &mut self.cmd
    }

    /// Get the final command to run the solver.
    pub fn done(self) -> SolverCmd {
        self.cmd
    }
}

impl Drop for SmtProc {
    fn drop(&mut self) {
        self.kill();
    }
}

impl SmtProc {
    /// Create a new SMT process by running a solver.
    ///
    /// The optional `tee` argument redirects all SMT output to a file, for
    /// debugging purposes.
    pub fn new(mut cmd: SolverCmd, tee: Option<&Path>) -> Result<Self> {
        cmd.option("produce-models", "true");
        cmd.option("produce-unsat-assumptions", "true");
        let mut child = Command::new(OsStr::new(&cmd.cmd))
            .args(cmd.args.iter().map(OsString::from))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .map_err(SolverError::from)?;
        let tee = match tee {
            Some(path) => {
                let mut f = Tee::new(path);
                f.append(Sexp::Comment(cmd.cmdline()));
                Some(f)
            }
            None => None,
        };
        let stdin = child.stdin.take().unwrap();
        let stdout = BufReader::new(child.stdout.take().unwrap());
        let mut proc = Self {
            child,
            stdin,
            stdout,
            tee,
            terminated: Arc::new(Mutex::new(false)),
        };
        for (option, val) in &cmd.options {
            proc.send(&app(
                "set-option",
                [atom_s(format!(":{option}")), atom_s(val)],
            ));
        }
        // silence a warning from CVC4/CVC5 when run manually without -q
        // TODO: figure out what a good default logic is (possibly will be
        // customized to the solver)
        proc.send(&app("set-logic", vec![atom_s("UFNIA")]));
        Ok(proc)
    }

    /// Get a handle to the process for cancellation.
    pub fn pid(&self) -> SmtPid {
        // this is a u32 -> i32 conversion which is very safe (Child already
        // guarantees a positive pid)
        let pid: u32 = self.child.id();
        let pid = Pid::from_raw(pid.try_into().unwrap());
        SmtPid {
            pid,
            terminated: self.terminated.clone(),
        }
    }

    /// Save the current tee file, if there is one. Returns the name of the
    /// created file (or None if there is no tee'd output setup).
    ///
    /// Errors are purely the result of I/O trying to save the file.
    pub fn save_tee(&self) -> Option<PathBuf> {
        self.tee.as_ref().and_then(|tee| match tee.save() {
            Ok(name) => Some(name),
            Err(err) => {
                // report this error but this isn't fatal so don't panic
                eprintln!("failed to save tee: {err}");
                None
            }
        })
    }

    /// Low-level API to send the solver a command as an s-expression. This
    /// should only be used for commands that do not require a response.
    pub fn send(&mut self, data: &sexp::Sexp) {
        writeln!(self.stdin, "{data}").expect("I/O error: failed to send to solver");
        if let Some(f) = &mut self.tee {
            f.append(data.clone());
        }
    }

    /// Low-level API to send the solver a command that expects a response,
    /// which is parsed as a single s-expression.
    pub fn send_with_reply(&mut self, data: &sexp::Sexp) -> Result<sexp::Sexp> {
        self.send(data);
        self.get_sexp()
    }

    /// Add a comment to the tee'd file.
    ///
    /// The comment is passed as a closure, which is not evaluated if there is
    /// no tee'd smt2 file.
    pub fn comment_with<F>(&mut self, comment: F)
    where
        F: FnOnce() -> String,
    {
        if let Some(f) = &mut self.tee {
            let comment = comment();
            f.append(Sexp::Comment("".to_string()));
            f.append(Sexp::Comment(comment));
        }
    }

    /// Get some attribute using the SMT get-info command.
    pub fn get_info(&mut self, attribute: &str) -> Result<Sexp> {
        let resp = self.send_with_reply(&app("get-info", [atom_s(attribute)]))?;
        match resp {
            Sexp::List(s) => {
                assert_eq!(s.len(), 2);
                assert_eq!(
                    &s[0],
                    &atom_s(attribute),
                    "unexpected response to get-info {}",
                    &s[0],
                );
                Ok(s[1].clone())
            }
            _ => panic!("unexpected get-info format {resp}"),
        }
    }

    /// Parse an error message returned as an s-expression.
    fn parse_error(resp: &str) -> String {
        // Z3 returns check-sat errors as:
        // (error "error msg")
        // sat
        //
        // Thus we parse the result as a sequence of sexps and look for the
        // error sexp.
        let sexps = sexp::parse_many(resp)
            .unwrap_or_else(|err| panic!("could not parse error response {resp}: {err}"));
        let error_msg = sexps
            .iter()
            .filter_map(|s| {
                s.app().and_then(|(head, args)| {
                    if head == "error" && args.len() == 1 {
                        args[0].atom_s()
                    } else {
                        None
                    }
                })
            })
            .next();
        let msg = error_msg.unwrap_or_else(|| panic!("no error sexp found in {resp}"));
        msg.to_string()
    }

    fn parse_sat(&mut self, resp: &str) -> Result<SatResp> {
        if resp == "unsat" {
            return Ok(SatResp::Unsat);
        }
        if resp == "sat" {
            return Ok(SatResp::Sat);
        }
        if resp == "unknown" {
            let reason = self
                .get_info(":reason-unknown")
                .expect("could not get :reason-unknown");
            return Ok(SatResp::Unknown(reason.to_string()));
        }
        self.check_killed()?;
        let msg = Self::parse_error(resp);
        return Err(SolverError::UnexpectedClose(msg));
    }

    /// Send the solver `(check-sat)`. For unknown gets a reason, but does not
    /// call `(get-model)` for sat.
    pub fn check_sat(&mut self) -> Result<SatResp> {
        self.check_sat_assuming(&[])
    }

    /// Send the solver `(check-sat-assuming)` with some assumed variables
    /// (which must be atoms, literal symbols or their negations).
    ///
    /// The assumptions do not affect subsequent use of the solver.
    pub fn check_sat_assuming(&mut self, assumptions: &[Sexp]) -> Result<SatResp> {
        let cmd = if assumptions.is_empty() {
            app("check-sat", [])
        } else {
            app("check-sat-assuming", vec![sexp_l(assumptions.to_vec())])
        };
        self.send(&cmd);
        let sexp_resp = self.get_response(|s| s.to_string())?;
        let resp = self.parse_sat(&sexp_resp)?;
        if matches!(resp, SatResp::Unknown(_)) {
            if let Some(name) = self.save_tee() {
                eprintln!("unknown response to {}", name.display());
            }
        }
        Ok(resp)
    }

    /// Run `(get-unsat-assumptions)` following an unsat response to get the
    /// list of terms used in the proof.
    ///
    /// Fails if the previous command wasn't a check_sat or check_sat_assuming
    /// that returned unsat.
    pub fn get_unsat_assumptions(&mut self) -> Result<Vec<Sexp>> {
        let sexp = self.send_with_reply(&app("get-unsat-assumptions", vec![]))?;
        if let Sexp::List(ss) = sexp {
            Ok(ss)
        } else {
            panic!("malformed get-unsat-assumptions response: {sexp}")
        }
    }

    fn check_killed(&mut self) -> Result<()> {
        // check if the solver was killed and return a special error
        if let Some(status) = self.child.try_wait().unwrap() {
            // mark the process as terminated
            *self.terminated.lock().unwrap() = true;
            if status.signal() == Some(nix::libc::SIGKILL) {
                return Err(SolverError::Killed);
            }
        }
        return Ok(());
    }

    /// A marker for determining end of solver response.
    const DONE: &str = "<<DONE>>";

    /// Low-level mechanism to get a response. Note that this needs to be issued
    /// after each query that returns a response, since it sends a marker and
    /// waits for the solver to reach that marker.
    fn get_response<F, T>(&mut self, cb: F) -> Result<T>
    where
        F: FnOnce(&str) -> T,
    {
        match writeln!(self.stdin, r#"(echo "{}")"#, Self::DONE) {
            Ok(_) => {}
            Err(err) => {
                if err.kind() == ErrorKind::BrokenPipe {
                    self.check_killed()?
                }
                return Err(SolverError::from(err));
            }
        }
        self.stdin
            .flush()
            .expect("I/O error: failed to send to solver");
        // buf accumulates the entire response, which is read line-by-line
        // looking for the DONE marker.
        let mut buf = String::new();
        loop {
            let last_end = buf.len();
            // n is the number of bytes read (that is, the length of this line
            // including the newline)
            let n = self.stdout.read_line(&mut buf)?;
            if n == 0 {
                self.check_killed()?;
                let msg = Self::parse_error(&buf);
                return Err(SolverError::UnexpectedClose(msg));
            }
            // last line, without the newline
            let last_line = buf[last_end..last_end + n].trim_end();
            // Z3 doesn't put quotes and CVC does (quotes do follow SMT-LIB)
            if last_line == Self::DONE || last_line == format!("\"{}\"", Self::DONE) {
                let response = buf[..last_end].trim_end();
                return Ok(cb(response));
            }
        }
    }

    fn get_sexp(&mut self) -> Result<Sexp> {
        self.get_response(|s| sexp::parse(s).expect("could not parse solver response"))
    }

    fn kill(&mut self) {
        _ = writeln!(self.stdin, "(exit)");
        _ = self.stdin.flush();
        _ = self.child.kill();
        _ = self.child.wait();
        *self.terminated.lock().unwrap() = true;

        // NOTE: the below waits by polling every 10ms; `child.wait()` actually
        // runs the `wait()` syscall, which cleans up the child process. Without
        // it, the child becomes a "zombie process" that consumes a pid.

        // let wait_time = std::time::Duration::from_millis(10);
        // for _ in 0..100 {
        //     let join = self.child.try_wait().expect("could not wait for child");
        //     if join.is_some() {
        //         return;
        //     }
        //     std::thread::sleep(wait_time);
        // }
        // panic!("could not wait for solver to properly terminate");
    }
}

impl SmtPid {
    /// Kill the SMT process by pid.
    pub fn kill(&self) {
        if *self.terminated.lock().unwrap() {
            return;
        }
        let r = signal::kill(self.pid, signal::Signal::SIGKILL);
        *self.terminated.lock().unwrap() = true;
        match r {
            Ok(_) => (),
            Err(errno) => {
                if errno != Errno::ESRCH {
                    panic!("killing smt process failed with {errno}");
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{sync::mpsc, thread};

    use crate::{
        smtlib::{
            proc::{CvcConf, SatResp, SolverError, Z3Conf},
            sexp::{app, atom_s, parse},
        },
        solver::solver_path,
    };
    use eyre::Context;

    use super::SmtProc;

    #[test]
    fn test_check_sat_z3() {
        let z3 = Z3Conf::new(&solver_path("z3")).done();
        let mut solver = SmtProc::new(z3, None).unwrap();
        let response = solver.check_sat().wrap_err("could not check-sat").unwrap();
        assert!(
            matches!(response, SatResp::Sat { .. }),
            "should be sat, got {response:?}"
        );
    }

    #[test]
    fn test_get_model_z3() {
        let z3 = Z3Conf::new(&solver_path("z3")).done();
        let mut solver = SmtProc::new(z3, None).unwrap();
        solver.send(&app("declare-const", [atom_s("a"), atom_s("Bool")]));

        let e = parse("(assert (and a (not a)))").unwrap();
        solver.send(&e);

        let response = solver.check_sat().wrap_err("could not check-sat").unwrap();
        insta::assert_debug_snapshot!(response, @"Unsat");
    }

    #[test]
    /// Regression test for issue #14
    ///
    /// We tried to pass --strict-parsing by default, which causes CVC5 to
    /// reject (or b) (it requires 2 or more disjuncts to the or).
    fn test_cvc5_singleton_or() {
        let cvc5 = CvcConf::new_cvc5(&solver_path("cvc5")).done();
        let mut solver = if let Ok(solver) = SmtProc::new(cvc5, None) {
            solver
        } else {
            eprintln!("could not find cvc5, skipping test");
            return;
        };

        let e = parse("(assert (and (or true) (and false)))").unwrap();
        solver.send(&e);
        let response = solver.check_sat().wrap_err("could not check-sat").unwrap();
        insta::assert_debug_snapshot!(response, @"Unsat");
    }

    #[test]
    fn test_spawn_many() {
        let z3 = Z3Conf::new(&solver_path("z3")).done();
        let num_iters = 1000;
        for _ in 0..num_iters {
            let _ = SmtProc::new(z3.clone(), None).unwrap();
        }
    }

    #[test]
    fn test_cvc5_ill_formed() {
        let cvc = CvcConf::new_cvc5(&solver_path("cvc5")).done();
        let mut proc = SmtProc::new(cvc, None).unwrap();
        let e = parse("(assert (= and or))").unwrap();
        proc.send(&e);
        let r = proc.check_sat();
        insta::assert_display_snapshot!(r.unwrap_err());
    }

    #[test]
    fn test_cvc4_ill_formed() {
        let cvc = CvcConf::new_cvc4(&solver_path("cvc4")).done();
        let mut proc = SmtProc::new(cvc, None).unwrap();
        let e = parse("(assert (= and or))").unwrap();
        proc.send(&e);
        let r = proc.check_sat();
        insta::assert_display_snapshot!(r.unwrap_err());
    }

    #[test]
    fn test_z3_ill_formed() {
        let z3 = Z3Conf::new(&solver_path("z3")).done();
        let mut proc = SmtProc::new(z3, None).unwrap();
        // unbound symbol
        let e = parse("(assert p)").unwrap();
        proc.send(&e);
        let r = proc.check_sat();
        insta::assert_display_snapshot!(r.unwrap_err());
    }

    // TODO: this test is not robust: killing the solver at the wrong time
    // results in a broken pipe error somewhere in the code which isn't caught
    //
    // A more systematic solution is needed, either checking if the solver was
    // killed on any broken pipe error, or arranging to only kill the solver if
    // it's in a check_sat call.
    #[test]
    #[ignore]
    fn test_z3_kill() {
        let z3 = Z3Conf::new(&solver_path("z3")).done();
        let mut proc = SmtProc::new(z3, None).unwrap();
        let pid = proc.pid();
        let smt2_file = "
(reset)
(set-logic QF_FP)

(declare-const a Float32)
(declare-const b Float32)
(declare-const r0 Float32)
(declare-const r1 Float32)

(assert (= r0 (fp.abs a)))
(assert (= r1 (fp.abs b)))
(assert (not (= (fp.mul RNE r0 r1) (fp.mul RNE (fp.abs a) (fp.abs b)))))
(check-sat)
"
        .trim();
        for line in smt2_file.lines().filter(|line| !line.is_empty()) {
            proc.send(&parse(line).unwrap());
        }
        let (send, recv) = mpsc::channel();
        thread::spawn(move || {
            let r = proc.get_response(|s| s.to_string());
            send.send(r).unwrap();
        });
        pid.kill();
        let r = recv.recv().unwrap();
        match r {
            Ok(_) => {
                panic!("check-sat should not succeed");
            }
            Err(err) => {
                if !matches!(err, SolverError::Killed) {
                    panic!("wrong solver error {err}");
                }
            }
        }
    }
}
