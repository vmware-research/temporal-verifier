// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Manage a running SMT process.
//!
//! This is a low-level generic API for SMT-LIB solvers; the solver-specific
//! parts are captured by the [`SolverCmd`] passed to launch the solver and in
//! the code that parses models returned by [`SmtProc::check_sat`].

use crate::smtlib::sexp;
use std::{
    ffi::{OsStr, OsString},
    fs::{File, OpenOptions},
    io::{self, BufRead, BufReader, Write},
    path::Path,
    process::{Child, ChildStdin, ChildStdout, Command, Stdio},
};
use thiserror::Error;

use super::sexp::{app, atom_s, sexp_l, Sexp};

/// SmtProc wraps an instance of a solver process.
#[derive(Debug)]
pub struct SmtProc {
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
    tee: Option<File>,
}

/// SatResp is a solver's response to a `(check-sat)` or similar command.
///
/// For unknown it also returns the reason the solver provides.
#[derive(Debug, Clone)]
pub enum SatResp {
    /// The query is satisfiable.
    Sat,
    /// The query is unsatisfiable (and thus negated assertions are valid).
    Unsat,
    /// Unknown whether the query is sat or unsat. The reason is the one given
    /// by (get-info :reason-unknown).
    ///
    /// This can happen to a timeout or limitations of quantifier instantiation
    /// heuristics, for example.
    Unknown(String),
}

#[derive(Error, Debug)]
pub enum SolverError {
    #[error("some io went wrong")]
    Io(#[from] io::Error),
    #[error("solver unexpectedly exited:\n{0}")]
    UnexpectedClose(String),
}

type Result<T> = std::result::Result<T, SolverError>;

#[derive(Debug, Clone)]
pub struct SolverCmd {
    pub cmd: String,
    pub args: Vec<String>,
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

    fn option<S: AsRef<str>>(&mut self, name: &str, val: S) {
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

#[derive(Debug, Clone)]
pub struct Z3Conf(SolverCmd);

impl Z3Conf {
    pub fn new(cmd: &str) -> Self {
        let mut cmd = SolverCmd {
            cmd: cmd.to_string(),
            args: vec![],
            options: vec![],
        };
        cmd.args(["-in", "-smt2"]);
        cmd.option("model.completion", "true");
        let mut conf = Self(cmd);
        conf.timeout_ms(20000);
        conf
    }

    pub fn model_compact(&mut self) {
        self.0.option("model.compact", "true");
    }

    pub fn timeout_ms(&mut self, ms: usize) {
        self.0.option("timeout", format!("{ms}"));
    }

    /// Get the final command to run the solver.
    pub fn done(self) -> SolverCmd {
        self.0
    }
}

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

    pub fn new_cvc4(cmd: &str) -> Self {
        Self::new_cvc(cmd, /*version5*/ false)
    }

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
                let mut f = Self::tee(path)?;
                _ = writeln!(&mut f, ";; {}", cmd.cmdline());
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

    /// Create the tee file.
    fn tee<P: AsRef<Path>>(path: P) -> Result<File> {
        let f = OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(path)
            .map_err(SolverError::from)?;
        Ok(f)
    }

    /// Low-level API to send the solver a command as an s-expression. This
    /// should only be used for commands that do not require a response.
    pub fn send(&mut self, data: &sexp::Sexp) {
        writeln!(self.stdin, "{data}").expect("I/O error: failed to send to solver");
        if let Some(f) = &mut self.tee {
            // TODO: this should be pretty-printed
            writeln!(f, "{data}").unwrap();
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
            _ = writeln!(f);
            _ = writeln!(f, ";; {comment}");
        }
    }

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
        let msg = Self::parse_error(resp);
        return Err(SolverError::UnexpectedClose(msg));
    }

    /// Send the solver `(check-sat)`. For unknown gets a reason, but does not
    /// call `(get-model)` for sat.
    pub fn check_sat(&mut self) -> Result<SatResp> {
        self.send(&app("check-sat", []));
        let resp = self.get_response(|s| s.to_string())?;
        self.parse_sat(&resp)
    }

    pub fn check_sat_assuming(&mut self, assumptions: &[Sexp]) -> Result<SatResp> {
        self.send(&app(
            "check-sat-assuming",
            vec![sexp_l(assumptions.to_vec())],
        ));
        let resp = self.get_response(|s| s.to_string())?;
        self.parse_sat(&resp)
    }

    /// Run `(get-unsat-assumptions)` following an unsat response to get the
    /// list of terms used in the proof.
    ///
    /// Fails if the previous command wasn't a check_sat or check_sat_assuming
    /// that returned sat.
    #[allow(dead_code)]
    pub fn get_unsat_assumptions(&mut self) -> Result<Vec<Sexp>> {
        let sexp = self.send_with_reply(&app("get-unsat-assumptions", vec![]))?;
        if let Sexp::List(ss) = sexp {
            Ok(ss)
        } else {
            panic!("malformed get-unsat-assumptions response: {sexp}")
        }
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
        writeln!(self.stdin, r#"(echo "{}")"#, Self::DONE)
            .expect("I/O error: failed to send to solver");
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
                let msg = Self::parse_error(&buf);
                return Err(SolverError::UnexpectedClose(msg));
            }
            // last line, without the newline
            let last_line = &buf[last_end..last_end + n - 1];
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

#[cfg(test)]
mod tests {
    use crate::{
        smtlib::{
            proc::{CvcConf, SatResp, Z3Conf},
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
        // launching z3 is slow on macos so don't spawn too many
        #[cfg(target_os = "macos")]
        let num_iters = 200;
        #[cfg(not(target_os = "macos"))]
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
}
