// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use codespan_reporting::diagnostic::{Diagnostic, Label};
use std::rc::Rc;
use std::{fs, path::PathBuf, process};

use crate::solver::solver_path;
use crate::{
    fly::{self, parser::parse_error_diagonistic, printer, sorts},
    inference::run_fixpoint,
    solver::backends::{self, GenericBackend},
    verify::{verify_module, SolverConf},
};
use clap::Args;
use codespan_reporting::{
    files::SimpleFile,
    term::{
        self as terminal,
        termcolor::{ColorChoice, StandardStream},
    },
};

#[derive(clap::ValueEnum, Copy, Clone, Debug, PartialEq, Eq)]
enum SolverType {
    Z3,
    Cvc,
    Cvc4,
    Cvc5,
}

#[derive(clap::ValueEnum, Copy, Clone, Debug, PartialEq, Eq)]
enum ColorOutput {
    Never,
    Auto,
    Always,
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct SolverArgs {
    #[arg(value_enum, long, default_value_t = SolverType::Z3)]
    /// Solver to use (z3, cvc; or use cvc4 or cvc5 to force a particular solver)
    solver: SolverType,

    #[arg(long)]
    /// Full path to output SMT file to
    smt_file: Option<PathBuf>,

    #[arg(long)]
    /// Output smt2 file alongside input file
    smt: bool,
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct VerifyArgs {
    #[command(flatten)]
    solver: SolverArgs,

    #[arg(long)]
    /// Run Houdini on supplied invariants
    houdini: bool,

    /// File name for a .fly file
    file: String,
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct InferArgs {
    #[command(flatten)]
    solver: SolverArgs,

    #[arg(long)]
    /// Try to extend model traces before looking for CEX in the frame
    extend_models: bool,

    #[arg(long)]
    /// Try to decompose the transition relation disjunctively
    disj: bool,

    /// File name for a .fly file
    file: String,
}

#[derive(clap::Subcommand, Clone, Debug, PartialEq, Eq)]
enum Command {
    Verify(VerifyArgs),
    Infer(InferArgs),
    Print {
        /// File name for a .fly file
        file: String,
    },
    Inline {
        /// File name for a .fly file
        file: String,
    },
}

impl Command {
    fn file(&self) -> &str {
        match self {
            Command::Verify(VerifyArgs { file, .. }) => file,
            Command::Infer(InferArgs { file, .. }) => file,
            Command::Print { file, .. } => file,
            Command::Inline { file, .. } => file,
        }
    }
}

#[derive(clap::Parser, Debug)]
#[command(about, long_about=None)]
pub struct App {
    #[arg(value_enum, long, default_value_t = ColorOutput::Auto)]
    /// Control color output. Auto disables colors with TERM=dumb or
    /// NO_COLOR=true.
    color: ColorOutput,

    #[command(subcommand)]
    /// Command to run
    command: Command,
}

fn solver_default_bin(t: SolverType) -> &'static str {
    match t {
        SolverType::Z3 => "z3",
        SolverType::Cvc | SolverType::Cvc5 => "cvc5",
        SolverType::Cvc4 => "cvc4",
    }
}

impl SolverArgs {
    fn get_solver_conf(&self, fname: &String) -> SolverConf {
        let backend_type = match &self.solver {
            SolverType::Z3 => backends::SolverType::Z3,
            SolverType::Cvc | SolverType::Cvc5 => backends::SolverType::Cvc5,
            SolverType::Cvc4 => backends::SolverType::Cvc4,
        };
        let solver_bin = solver_path(solver_default_bin(self.solver));
        let tee: Option<PathBuf> = if let Some(path) = &self.smt_file {
            Some(path.to_path_buf())
        } else if self.smt {
            let path = PathBuf::from(fname).with_extension("smt2");
            Some(path)
        } else {
            None
        };
        SolverConf {
            backend: GenericBackend::new(backend_type, &solver_bin),
            tee,
        }
    }
}

impl VerifyArgs {
    fn get_solver_conf(&self) -> SolverConf {
        self.solver.get_solver_conf(&self.file)
    }
}

impl InferArgs {
    fn get_solver_conf(&self) -> SolverConf {
        self.solver.get_solver_conf(&self.file)
    }
}

impl App {
    pub fn exec(self) {
        let file = fs::read_to_string(self.command.file()).expect("could not read input file");
        let files = SimpleFile::new(self.command.file(), &file);

        let writer = StandardStream::stderr(match &self.color {
            ColorOutput::Never => ColorChoice::Never,
            ColorOutput::Always => ColorChoice::Always,
            ColorOutput::Auto => ColorChoice::Auto,
        });
        let config = codespan_reporting::term::Config {
            start_context_lines: 3,
            end_context_lines: 3,
            ..Default::default()
        };

        let m = match fly::parse(&file) {
            Ok(v) => v,
            Err(err) => {
                let diagnostic = parse_error_diagonistic((), &err);
                terminal::emit(&mut writer.lock(), &config, &files, &diagnostic).unwrap();
                process::exit(1);
            }
        };

        let r = sorts::check(&m);
        if let Err((err, span)) = r {
            eprintln!("sort checking error:");

            let mut diagnostic = Diagnostic::error().with_message(format!("{}", err));
            if let Some(span) = span {
                diagnostic = diagnostic.with_labels(vec![Label::primary((), span.start..span.end)]);
            }
            terminal::emit(&mut writer.lock(), &config, &files, &diagnostic).unwrap();

            process::exit(1);
        }

        match self.command {
            Command::Print { .. } => {
                println!("{}", printer::fmt(&m));
            }
            Command::Verify(ref args @ VerifyArgs { houdini, .. }) => {
                let conf = args.get_solver_conf();
                let r = verify_module(&conf, &m, houdini);
                match r {
                    Ok(()) => println!("verifies!"),
                    Err(err) => {
                        eprintln!("verification errors:");

                        for fail in &err.fails {
                            let diagnostic = fail.diagnostic(());
                            terminal::emit(&mut writer.lock(), &config, &files, &diagnostic)
                                .unwrap();
                        }

                        process::exit(1);
                    }
                }
            }
            Command::Infer(ref args @ InferArgs { .. }) => {
                let conf = Rc::new(args.get_solver_conf());
                run_fixpoint(conf, &m, args.extend_models, args.disj);
            }
            Command::Inline { .. } => {
                let mut m = m;
                m.inline_defs();
                println!("{}", printer::fmt(&m));
            }
        }
    }
}
