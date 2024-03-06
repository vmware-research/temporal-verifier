// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Manage a running SMT process.
//!
//! This is a low-level generic API for SMT-LIB solvers; the solver-specific
//! parts are captured by the [`SolverCmd`] passed to launch the solver and in
//! the code that parses models returned by [`SmtProc::check_sat`].

use crate::conf::SolverCmd;
use crate::sexp;
use crate::tee::Tee;
use nix::{errno::Errno, sys::signal, unistd::Pid};
use std::{
    ffi::{OsStr, OsString},
    io::{self, BufRead, BufReader, ErrorKind, Write},
    path::{Path, PathBuf},
    process::{Child, ChildStdin, ChildStdout, Command, Stdio},
    sync::{Arc, RwLock},
};
use thiserror::Error;

use super::sexp::{app, atom_s, sexp_l, Sexp};

/// The states that the process can be in.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum Status {
    /// Solver is running normally. If `in_call` is true, it is currently
    /// processing a `check-sat` or `get-model` call.
    Running { in_call: bool },
    /// A cancellation has been requested but has not been acted upon because
    /// the solver isn't at a stopping point (an expensive call). Any solver
    /// operations after this point will cause the solver to be killed; calls
    /// that return nothing like `assert` will silently succeed, while calls
    /// that require a response will return `SolverError::Killed`.
    Stopping,
    /// The solver has been killed but needs a `.wait()` call to reap the process.
    NeedsWait,
    /// The solver has exited and the process has been reaped with `.wait()`.
    Terminated,
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
    terminated: Arc<RwLock<Status>>,
}

/// A handle to the SMT process for cancelling an in-progress check.
#[derive(Clone)]
pub struct SmtPid {
    pid: Pid,
    terminated: Arc<RwLock<Status>>,
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
    #[error("some I/O went wrong: {0}")]
    Io(#[from] io::Error),
    /// Could not minimize
    #[error("could not minimize:\n{0}")]
    CouldNotMinimize(String),
    /// Solver returned an `(error ...)` response
    #[error("solver returned an error:\n{0}")]
    UnexpectedClose(String),
    /// Solver killed specifically by SIGKILL signal
    #[error("solver was killed")]
    Killed,
}

type Result<T> = std::result::Result<T, SolverError>;

// =============================
// State-machine related code
// =============================

impl Drop for SmtProc {
    fn drop(&mut self) {
        self.kill();
    }
}

impl SmtPid {
    /// Kill the SMT process by pid.
    pub fn kill(&self) {
        let mut terminated = self.terminated.write().unwrap();
        match *terminated {
            Status::NeedsWait | Status::Terminated | Status::Stopping => {
                return;
            }
            Status::Running { in_call } => {
                // Only try to kill the solver if it's in the middle of an
                // expensive call (currently check-sat and get-model).
                if in_call {
                    let r = signal::kill(self.pid, signal::Signal::SIGKILL);
                    if let Err(errno) = r {
                        if errno != Errno::ESRCH {
                            panic!("killing SMT process {} failed with {errno}", self.pid);
                        }
                    }
                    *terminated = Status::NeedsWait;
                } else {
                    // Otherwise, we mark the solver as stopping, which causes
                    // most commands to exit early and the next check-sat or
                    // get-model to kill the solver without running.
                    *terminated = Status::Stopping;
                }
            }
        }
    }

    /// Check whether the SMT process has been killed (or is being killed).
    pub fn is_killed(&self) -> bool {
        let terminated = self.terminated.read().unwrap();
        matches!(
            *terminated,
            Status::NeedsWait | Status::Terminated | Status::Stopping
        )
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
            terminated: Arc::new(RwLock::new(Status::Running { in_call: false })),
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

    fn send_raw(&mut self, data: &sexp::Sexp) {
        writeln!(self.stdin, "{data}").expect("I/O error: failed to send to solver");
        if let Some(f) = &mut self.tee {
            f.append(data.clone());
        }
    }

    /// Low-level API to send the solver a command that expects a response,
    /// which is parsed as a single s-expression.
    fn send_with_reply(&mut self, data: &sexp::Sexp) -> Result<sexp::Sexp> {
        self.send(data);
        self.get_response(|s| sexp::parse(s).expect("could not parse solver response"))
    }

    /// Get an error presumed to be in resp, checking for termination first.
    ///
    /// This function always returns a `Result::Err`, but is written this way for
    /// convenient use with `?`. As a result it can return a `Result<T>` for any
    /// type `T`.
    fn get_error<T>(&mut self, resp: &str) -> Result<T> {
        self.check_killed()?;
        let msg = Self::parse_error(resp);
        return Err(SolverError::UnexpectedClose(msg));
    }

    /// Check the status because the solver is currently idle, to see if we
    /// should kill or wait and return early.
    fn handle_termination_status(&mut self, status: &mut Status) -> Result<()> {
        match *status {
            Status::Running { .. } => return Ok(()),
            Status::Stopping => {
                self.child
                    .kill()
                    .expect("could not kill after cancellation request");
                self.child
                    .wait()
                    .expect("could not wait after cancellation request");
            }
            Status::NeedsWait => {
                self.child
                    .wait()
                    .expect("could not wait for terminated child");
            }
            Status::Terminated => {}
        }
        // if not currently running, we'll leave the solver terminated and `wait`'d for
        *status = Status::Terminated;
        return Err(SolverError::Killed);
    }

    /// Mark the solver as being inside an expensive call (so killing it will
    /// actually send a signal).
    fn start_call(&mut self) -> Result<()> {
        let status_m = self.terminated.clone();
        let mut status = status_m.write().unwrap();
        self.handle_termination_status(&mut status)?;
        assert!(
            *status == Status::Running { in_call: false },
            "unexpected start when solver is already in a call"
        );
        *status = Status::Running { in_call: true };
        Ok(())
    }

    /// Mark the solver as being done with an expensive call.
    fn end_call(&mut self) -> Result<()> {
        let status_m = self.terminated.clone();
        let mut status = status_m.write().unwrap();
        self.handle_termination_status(&mut status)?;
        assert!(
            *status == Status::Running { in_call: true },
            "unexpected end when solver is not in a call"
        );
        *status = Status::Running { in_call: false };
        Ok(())
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
        self.start_call()?;
        let sexp_resp = self.get_response(|s| s.to_string())?;
        let resp = self.parse_sat(&sexp_resp)?;
        if matches!(resp, SatResp::Unknown(_)) {
            if let Some(name) = self.save_tee() {
                eprintln!("unknown response to {}", name.display());
            }
        }
        self.end_call()?;
        Ok(resp)
    }

    fn check_killed(&mut self) -> Result<()> {
        let status_m = self.terminated.clone();
        let mut status = status_m.write().unwrap();
        self.handle_termination_status(&mut status)?;
        Ok(())
    }

    /// A marker for determining end of solver response.
    const DONE: &'static str = "<<DONE>>";

    fn write_stdin(&mut self, line: &str) -> std::result::Result<(), io::Error> {
        writeln!(self.stdin, "{line}")?;
        self.stdin.flush()?;
        Ok(())
    }

    /// Low-level mechanism to get a response. Note that this needs to be issued
    /// after each query that returns a response, since it sends a marker and
    /// waits for the solver to reach that marker.
    fn get_response<F, T>(&mut self, cb: F) -> Result<T>
    where
        F: FnOnce(&str) -> T,
    {
        match self.write_stdin(&format!(r#"(echo "{}")"#, Self::DONE)) {
            Ok(_) => {}
            Err(err) => {
                if err.kind() == ErrorKind::BrokenPipe {
                    self.check_killed()?
                }
                return Err(SolverError::from(err));
            }
        }
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

    fn kill(&mut self) {
        _ = writeln!(self.stdin, "(exit)");
        _ = self.stdin.flush();
        _ = self.child.kill();
        _ = self.child.wait();
        *self.terminated.write().unwrap() = Status::Terminated;
    }

    // ========================
    // Non state machine APIs
    // ========================

    /// Low-level API to send the solver a command as an s-expression. This
    /// should only be used for commands that do not require a response.
    pub fn send(&mut self, data: &sexp::Sexp) {
        let status_m = self.terminated.clone();
        let mut status = status_m.write().unwrap();
        if self.handle_termination_status(&mut status).is_err() {
            // solver has been cancelled, pretend like the command succeeded
            return;
        }
        drop(status);
        self.send_raw(data)
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
        self.get_error(resp)
    }

    /// Send the solver `(check-sat)`. For unknown gets a reason, but does not
    /// call `(get-model)` for sat.
    pub fn check_sat(&mut self) -> Result<SatResp> {
        self.check_sat_assuming(&[])
    }

    /// Get a model (following a sat reply) as an s-expression.
    pub fn get_model(&mut self) -> Result<Sexp> {
        self.start_call()?;
        let model = self.send_with_reply(&app("get-model", []))?;
        self.end_call()?;
        Ok(model)
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

    // =============
    // Tee support
    // =============

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
}

#[cfg(test)]
mod tests {
    use crate::{
        conf::{CvcConf, Z3Conf},
        path::solver_path,
        proc::{SatResp, SmtProc, SolverError},
        sexp::{app, atom_s, parse},
    };
    use eyre::Context;
    use std::{sync::mpsc, thread, time::Duration};

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

    #[test]
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
"
        .trim();
        for line in smt2_file.lines().filter(|line| !line.is_empty()) {
            proc.send(&parse(line).unwrap());
        }
        let (send, recv) = mpsc::channel();
        thread::spawn(move || {
            let r = proc.check_sat();
            send.send(r).unwrap();
        });
        // wait for check-sat to start
        thread::sleep(Duration::from_millis(50));
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

    #[test]
    fn test_kill_before_send() {
        let z3 = Z3Conf::new(&solver_path("z3")).done();
        let mut proc = SmtProc::new(z3, None).unwrap();
        let pid = proc.pid();

        proc.send(&parse("(reset)").unwrap());
        proc.send(&parse("(set-logic QF_FP)").unwrap());

        // this kill will just tell the solver to ignore commands until check_sat().
        pid.kill();

        let smt2_file = "
(declare-const a Float32)
(declare-const b Float32)
(declare-const r0 Float32)
(declare-const r1 Float32)

(assert (= r0 (fp.abs a)))
(assert (= r1 (fp.abs b)))
(assert (not (= (fp.mul RNE r0 r1) (fp.mul RNE (fp.abs a) (fp.abs b)))))
"
        .trim();

        for line in smt2_file.lines().filter(|line| !line.is_empty()) {
            proc.send(&parse(line).unwrap());
        }
        // this should immediately return an error and kill the solver
        match proc.check_sat() {
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
