// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! The temporal-verifier binary's command-line interface.

use bounded::checker::CheckerAnswer;
use codespan_reporting::diagnostic::{Diagnostic, Label};
use inference::qalpha::fixpoint::defaults;
use path_slash::PathExt;
use solver::basics::SingleSolver;
use std::collections::HashMap;
use std::path::Path;
use std::sync::Arc;
use std::{fs, process};

use clap::Args;
use codespan_reporting::{
    files::SimpleFile,
    term::{
        self as terminal,
        termcolor::{ColorChoice, StandardStream},
    },
};
use fly::semantics::models_to_string;
use fly::syntax::{Module, Signature, Sort};
use fly::{self, parser::parse_error_diagnostic, printer, sorts, timing};
use inference::basics::{
    FOModule, QalphaConfig, QfBody, QuantifierFreeConfig, SimulationConfig, SmtTactic,
};
use inference::houdini;
use inference::qalpha::{
    fixpoint::{self, qalpha_dynamic, Strategy},
    quant::{parse_quantifier, QuantifierConfig},
};
use inference::updr::Updr;
use solver::backends;
use solver::conf::SolverConf;
use verify::module::verify_module;

#[derive(clap::ValueEnum, Copy, Clone, Debug, PartialEq, Eq)]
enum SolverType {
    Z3,
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
    // --solver and --smt are global, meaning they are allowed even after
    // subcommands
    #[arg(value_enum, long, default_value_t = SolverType::Z3, global = true)]
    /// Solver to use
    solver: SolverType,

    #[arg(long, global = true)]
    /// Output smt2 file alongside input file
    smt: bool,

    #[arg(long, default_value_t = 600, global = true)]
    /// SMT solver timeout in seconds
    timeout: usize,

    #[arg(long, default_value_t = 0, global = true)]
    /// SMT solver random seed
    solver_seed: usize,
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct VerifyArgs {
    #[command(flatten)]
    solver: SolverArgs,

    #[arg(long)]
    /// Print timing statistics
    time: bool,

    /// File name for a .fly file
    file: String,
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct QuantifierConfigArgs {
    #[arg(short, long)]
    /// Sorts in the order they should appear in the quantifier prefix
    sort: Vec<String>,

    #[arg(short, long)]
    /// Quantifiers in the form `<quantifier: F/E/*> <sort> <count>`
    quantifier: Vec<String>,
}

impl QuantifierConfigArgs {
    fn to_cfg(&self, sig: &Signature) -> QuantifierConfig {
        let mut quantifiers;
        let mut sorts: Vec<Sort>;
        let mut counts: Vec<usize>;
        if !self.quantifier.is_empty() {
            quantifiers = vec![];
            sorts = vec![];
            counts = vec![];
            for quantifier_spec in &self.quantifier {
                let r = parse_quantifier(sig, quantifier_spec);
                match r {
                    Ok((q, sort, count)) => {
                        quantifiers.push(q);
                        sorts.push(sort);
                        counts.push(count);
                    }
                    Err(err) => panic!("{err}"),
                }
            }
        } else if !self.sort.is_empty() {
            sorts = self
                .sort
                .iter()
                .map(|s| Sort::Uninterpreted(s.clone()))
                .collect();
            quantifiers = vec![None; sorts.len()];
            counts = vec![fixpoint::defaults::QUANT_SAME_SORT; sorts.len()];
        } else {
            sorts = sig.sorts.iter().map(|s| Sort::uninterpreted(s)).collect();
            quantifiers = vec![None; sorts.len()];
            counts = vec![fixpoint::defaults::QUANT_SAME_SORT; sorts.len()];
        }
        QuantifierConfig::new(Arc::new(sig.clone()), quantifiers, sorts, &counts)
    }
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct QuantifierFreeConfigArgs {
    #[arg(long)]
    /// Defines the type of quantifier-free body (cnf/dnf/pdnf)
    qf: Option<String>,

    #[arg(long)]
    /// Determines the maximal size of each clause
    clause_size: Option<usize>,

    #[arg(long)]
    /// Determines the maximal number of cubes in disjunction
    cubes: Option<usize>,

    #[arg(long)]
    /// The maximal nesting depth of terms in the vocabulary (unbounded if not provided)
    nesting: Option<usize>,

    #[arg(long, action)]
    /// Do not include equality terms in the vocabulary
    no_include_eq: bool,
}

impl QuantifierFreeConfigArgs {
    fn to_cfg(&self) -> QuantifierFreeConfig {
        QuantifierFreeConfig {
            qf_body: self.qf.as_ref().map_or(QfBody::default(), |qf| qf.into()),
            clause_size: self.clause_size,
            cubes: self.cubes,
            nesting: self.nesting,
        }
    }
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct SimulationConfigArgs {
    /// What size bound to use for the given sort in simulations, given as SORT=N as in --bound node=2
    #[arg(long)]
    bound: Vec<String>,

    /// Instead of a bound for each sort, bound the sum of sort sizes
    #[arg(long)]
    bound_sum: Option<usize>,

    #[arg(long)]
    /// Run simulations up to this depth
    depth: Option<usize>,

    #[arg(long)]
    /// In simulations, consider the depth from the last counterexample found
    guided: bool,

    #[arg(long)]
    /// Run simulations in a DFS manner (default is BFS)
    dfs: bool,
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct InferenceConfigArgs {
    #[command(flatten)]
    quant_cfg: QuantifierConfigArgs,

    #[arg(long)]
    /// Number of different seeds to try the solvers with
    seeds: Option<usize>,

    #[arg(long)]
    /// Do not try to decompose the transition relation disjunctively
    no_disj: bool,

    #[arg(long)]
    /// How to perform the SMT queries (full/gradual/minimal)
    smt_tactic: Option<String>,
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct QalphaArgs {
    #[command(flatten)]
    infer_cfg: InferenceConfigArgs,

    #[command(flatten)]
    sim_cfg: SimulationConfigArgs,

    #[command(flatten)]
    qf_cfg: QuantifierFreeConfigArgs,

    #[arg(long)]
    /// Use the baseline implementation the data structures in qalpha
    baseline: bool,

    #[arg(long)]
    /// Determines the strategy that is used in addition to the simulations.
    /// Options are "weaken", "weaken-pd", "houdini", "houdini-pd", or "none".
    /// "pd" indicates a property-directed strategy.
    strategy: Option<String>,

    #[arg(long)]
    /// Launch no new runs after safety has been proven
    until_safe: bool,

    /// File name for a .fly file
    file: String,
}

impl QalphaArgs {
    fn to_cfg(&self, m: &Module, fname: String) -> QalphaConfig {
        let universe = if self.sim_cfg.bound.is_empty() || self.sim_cfg.bound_sum.is_some() {
            vec![defaults::SIMULATION_SORT_SIZE; m.signature.sorts.len()]
        } else {
            let universe_map = get_universe(&m.signature, &self.sim_cfg.bound);
            m.signature.sorts.iter().map(|s| universe_map[s]).collect()
        };
        QalphaConfig {
            fname,
            fo: FOModule::new(
                m,
                !self.infer_cfg.no_disj,
                self.infer_cfg
                    .smt_tactic
                    .as_ref()
                    .map_or(SmtTactic::default(), |s| s.into()),
            ),

            quant_cfg: Arc::new(self.infer_cfg.quant_cfg.to_cfg(&m.signature)),

            qf_cfg: self.qf_cfg.to_cfg(),

            sim: SimulationConfig {
                universe,
                sum: self.sim_cfg.bound_sum,
                depth: self.sim_cfg.depth,
                guided: self.sim_cfg.guided,
                dfs: self.sim_cfg.dfs,
            },

            strategy: self
                .strategy
                .as_ref()
                .map_or(Strategy::default(), |s| s.into()),
            until_safe: self.until_safe,
            seeds: self.infer_cfg.seeds.unwrap_or(1),
            baseline: self.baseline,
        }
    }
}

#[derive(clap::Subcommand, Clone, Debug, PartialEq, Eq)]
enum InferCommand {
    /// Run Houdini
    Houdini {
        /// File name for a .fly file
        file: String,
    },
    /// Run quantified-alpha-from-below
    Qalpha(QalphaArgs),
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct InferArgs {
    #[command(flatten)]
    solver: SolverArgs,

    #[arg(long, global = true)]
    /// Print timing statistics
    time: bool,

    #[arg(long)]
    /// Don't print non-deterministic details about the run, e.g., the found invariant or timing information (for testing)
    no_print_nondet: bool,

    #[command(subcommand)]
    infer_cmd: InferCommand,
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct BoundedArgs {
    /// File name for a .fly file
    file: String,
    /// Maximum number of transitions to consider during model checking
    #[arg(long)]
    depth: Option<usize>,
    /// What size bound to use for the given sort, given as SORT=N as in --bound node=2
    #[arg(long)]
    bound: Vec<String>,
    /// Whether or not to print timing information (true by default)
    #[arg(long)]
    print_timing: Option<bool>,
}

/// Parses the arguments in `bound` into a universe size map.
///
/// Ensures that every sort in the given signature is given a bound.
fn get_universe(sig: &Signature, bound: &[String]) -> HashMap<String, usize> {
    let mut universe: HashMap<String, usize> = HashMap::new();
    for b in bound {
        if let [sort_name, bound_size] = b.split('=').collect::<Vec<&str>>()[..] {
            let sort_name = sort_name.to_string();
            if !sig.sorts.contains(&sort_name) {
                eprintln!("unknown sort name {sort_name} in bound {b}");
                process::exit(1);
            }
            if let Ok(bound_size) = bound_size.parse::<usize>() {
                universe.insert(sort_name, bound_size);
            } else {
                eprintln!("could not parse bound as integer in {b}");
                process::exit(1);
            }
        } else {
            eprintln!("expected exactly one '=' in bound {b}");
            process::exit(1);
        }
    }
    if let Some(unbounded_sort) = sig.sorts.iter().find(|&s| !universe.contains_key(s)) {
        eprintln!(
            "need a bound for sort {unbounded_sort} on the command line, as in --bound {unbounded_sort}=N"
        );
        process::exit(1);
    }
    universe
}

impl BoundedArgs {
    /// Parses the arguments in self.bound into a universe size map.
    ///
    /// Ensures that every sort in the given signature is given a bound.
    fn get_universe(&self, sig: &Signature) -> HashMap<String, usize> {
        get_universe(sig, &self.bound)
    }
}

#[derive(clap::Subcommand, Clone, Debug, PartialEq, Eq)]
enum Command {
    /// Verify all assertions using user-provided invariants.
    Verify(VerifyArgs),
    /// Verify assertions by inferring invariants with UPDR.
    UpdrVerify(VerifyArgs),
    /// Infer invariants using other invariant inference algorithms.
    Infer(InferArgs),
    /// Parse and re-print a fly file (for debugging)
    Print {
        /// File name for a .fly file
        file: String,
    },
    /// Parse a fly file, inline definitions, and print (for debugging)
    Inline {
        /// File name for a .fly file
        file: String,
    },
    /// Apply bounded model checking to each assertion using a set of states.
    SetCheck {
        #[command(flatten)]
        bounded: BoundedArgs,
        /// Whether to only keep track of the last state of the trace
        #[arg(long)]
        compress_traces: bool,
    },
    /// Apply bounded model checking to each assertion using a SAT solver.
    SatCheck(BoundedArgs),
    /// Apply bounded model checking to each assertion using binary decision
    /// diagrams (BDDs).
    BddCheck {
        #[command(flatten)]
        bounded: BoundedArgs,
        /// Whether to search from the unsafe states inward
        #[arg(long)]
        reversed: bool,
    },
    /// Apply bounded model checking to each assertion using an SMT solver.
    SmtCheck {
        #[command(flatten)]
        bounded: BoundedArgs, // universe bounds are unused
        #[command(flatten)]
        solver: SolverArgs,
    },
}

impl InferCommand {
    fn file(&self) -> &str {
        match self {
            InferCommand::Houdini { file } => file,
            InferCommand::Qalpha(QalphaArgs { file, .. }) => file,
        }
    }
}

impl Command {
    fn file(&self) -> &str {
        match self {
            Command::Verify(VerifyArgs { file, .. }) => file,
            Command::Infer(InferArgs { infer_cmd, .. }) => infer_cmd.file(),
            Command::UpdrVerify(VerifyArgs { file, .. }) => file,
            Command::Print { file, .. } => file,
            Command::Inline { file, .. } => file,
            Command::SetCheck {
                bounded: BoundedArgs { file, .. },
                ..
            } => file,
            Command::SatCheck(BoundedArgs { file, .. }) => file,
            Command::BddCheck {
                bounded: BoundedArgs { file, .. },
                ..
            } => file,
            Command::SmtCheck {
                bounded: BoundedArgs { file, .. },
                ..
            } => file,
        }
    }
}

#[derive(clap::Parser, Debug)]
#[command(about, long_about=None)]
/// Entrypoint for the temporal-verifier binary, including all commands.
pub struct App {
    #[arg(value_enum, long, default_value_t = ColorOutput::Auto)]
    /// Control color output. Auto disables colors with TERM=dumb or
    /// NO_COLOR=true.
    color: ColorOutput,

    #[command(subcommand)]
    /// Command to run
    command: Command,
}

impl SolverArgs {
    fn get_solver_conf(&self, fname: &String) -> SolverConf {
        let backend_type = match &self.solver {
            SolverType::Z3 => backends::SolverType::Z3,
            SolverType::Cvc5 => backends::SolverType::Cvc5,
            SolverType::Cvc4 => backends::SolverType::Cvc4,
        };

        SolverConf::new(
            backend_type,
            self.smt,
            fname,
            self.timeout,
            self.solver_seed,
        )
    }
}

impl VerifyArgs {
    fn get_solver_conf(&self) -> SolverConf {
        self.solver.get_solver_conf(&self.file)
    }
}

impl InferArgs {
    fn get_solver_conf(&self) -> SolverConf {
        self.solver
            .get_solver_conf(&self.infer_cmd.file().to_string())
    }
}

impl App {
    /// Run the application.
    pub fn exec(self) {
        let file = fs::read_to_string(self.command.file()).expect("could not read input file");
        // We make sure paths look like Unix paths on all platforms, otherwise test snapshots don't match.
        let standardized_filename = Path::new(self.command.file()).to_slash_lossy();
        let files = SimpleFile::new(standardized_filename, &file);

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

        let mut m = match fly::parser::parse(&file) {
            Ok(v) => v,
            Err(err) => {
                let diagnostic = parse_error_diagnostic((), &err);
                terminal::emit(&mut writer.lock(), &config, &files, &diagnostic).unwrap();
                process::exit(1);
            }
        };

        let r = sorts::sort_check_module(&mut m);
        if let Err((err, span)) = r {
            eprintln!("sort checking error:");

            let mut diagnostic = Diagnostic::error().with_message(format!("{err}"));
            if let Some(span) = span {
                diagnostic = diagnostic.with_labels(vec![Label::primary((), span.start..span.end)]);
            }
            terminal::emit(&mut writer.lock(), &config, &files, &diagnostic).unwrap();

            process::exit(1);
        }

        match self.command {
            Command::Print { .. } => {
                // don't inline for printing
                println!("{}", printer::fmt(&m));
            }
            Command::Verify(ref args) => {
                let conf = args.get_solver_conf();
                m.inline_defs();
                let r = verify_module(&conf, &m);
                if args.time {
                    timing::report();
                }
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
            Command::Infer(
                ref args @ InferArgs {
                    infer_cmd: InferCommand::Houdini { .. },
                    ..
                },
            ) => {
                let conf = args.get_solver_conf();
                m.inline_defs();
                let r = houdini::infer_module(&conf, &m);
                if args.time {
                    timing::report();
                }
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
            Command::Infer(
                ref args @ InferArgs {
                    infer_cmd: InferCommand::Qalpha(ref qargs),
                    ..
                },
            ) => {
                m.inline_defs();
                let infer_cfg = Arc::new(qargs.to_cfg(&m, args.infer_cmd.file().to_string()));
                qalpha_dynamic(infer_cfg, &m, !args.no_print_nondet);
                if args.time {
                    timing::report();
                }
            }
            Command::Inline { .. } => {
                let mut m = m;
                m.inline_defs();
                println!("{}", printer::fmt(&m));
            }
            Command::UpdrVerify(ref args @ VerifyArgs { .. }) => {
                let conf = Arc::new(SingleSolver::new(args.get_solver_conf()));
                let mut updr = Updr::new(conf);
                let _result = updr.search(&m);
            }

            Command::SetCheck {
                bounded,
                compress_traces,
            } => {
                m.inline_defs();
                let back_convert_model = match m.convert_non_bool_relations() {
                    Ok(f) => f,
                    Err(e) => {
                        eprintln!("{e}");
                        process::exit(1)
                    }
                };
                let univ = bounded.get_universe(&m.signature);
                match bounded::set::check(
                    &m,
                    &univ,
                    bounded.depth,
                    compress_traces.into(),
                    bounded.print_timing.unwrap_or(true),
                ) {
                    Ok(CheckerAnswer::Counterexample(models)) => {
                        println!(
                            "found counterexample:\n{}",
                            models_to_string(models.iter().map(back_convert_model))
                        )
                    }
                    Ok(CheckerAnswer::Unknown) => {
                        println!(
                            "answer: safe up to {} for given sort bounds",
                            bounded
                                .depth
                                .map(|d| format!("depth {d}"))
                                .unwrap_or("any depth".to_string())
                        );
                    }
                    Ok(CheckerAnswer::Convergence(())) => {
                        println!("answer: safe forever with given sort bounds")
                    }
                    Err(error) => eprintln!("{error}"),
                }
            }
            Command::SatCheck(bounded) => {
                m.inline_defs();
                let back_convert_model = match m.convert_non_bool_relations() {
                    Ok(f) => f,
                    Err(e) => {
                        eprintln!("{e}");
                        process::exit(1)
                    }
                };
                let depth = match bounded.depth {
                    Some(depth) => depth,
                    None => {
                        eprintln!("sat checker does not support unbounded depth. please specify --depth N on the command line");
                        process::exit(1)
                    }
                };
                let univ = bounded.get_universe(&m.signature);
                match bounded::sat::check(&m, &univ, depth, bounded.print_timing.unwrap_or(true)) {
                    Ok(CheckerAnswer::Counterexample(models)) => {
                        println!(
                            "found counterexample:\n{}",
                            models_to_string(models.iter().map(back_convert_model))
                        )
                    }
                    Ok(CheckerAnswer::Unknown) => {
                        println!("answer: safe up to depth {depth} for given sort bounds")
                    }
                    Ok(CheckerAnswer::Convergence(())) => unreachable!(),
                    Err(error) => eprintln!("{error}"),
                }
            }
            Command::BddCheck { bounded, reversed } => {
                m.inline_defs();
                let back_convert_model = match m.convert_non_bool_relations() {
                    Ok(f) => f,
                    Err(e) => {
                        eprintln!("{e}");
                        process::exit(1)
                    }
                };
                let univ = bounded.get_universe(&m.signature);
                let check = match reversed {
                    false => bounded::bdd::check,
                    true => bounded::bdd::check_reversed,
                };
                match check(
                    &m,
                    &univ,
                    bounded.depth,
                    bounded.print_timing.unwrap_or(true),
                ) {
                    Ok(CheckerAnswer::Counterexample(models)) => {
                        println!(
                            "found counterexample:\n{}",
                            models_to_string(models.iter().map(back_convert_model))
                        )
                    }
                    Ok(CheckerAnswer::Unknown) => {
                        println!(
                            "answer: safe up to {} for given sort bounds",
                            bounded
                                .depth
                                .map(|d| format!("depth {d}"))
                                .unwrap_or("any depth".to_string())
                        );
                    }
                    Ok(CheckerAnswer::Convergence(..)) => {
                        println!("answer: safe forever with given sort bounds")
                    }
                    Err(error) => eprintln!("{error}"),
                }
            }
            Command::SmtCheck { bounded, solver } => {
                m.inline_defs();
                let depth = match bounded.depth {
                    Some(depth) => depth,
                    None => {
                        eprintln!("smt checker does not support unbounded depth. please specify --depth N on the command line");
                        process::exit(1)
                    }
                };
                match bounded::smt::check(
                    &m,
                    &solver.get_solver_conf(&file),
                    depth,
                    bounded.print_timing.unwrap_or(true),
                ) {
                    Ok(CheckerAnswer::Counterexample(models)) => {
                        println!("found counterexample:\n{}", models_to_string(models))
                    }
                    Ok(CheckerAnswer::Unknown) => {
                        println!("answer: safe up to depth {depth} for given sort bounds")
                    }
                    Ok(CheckerAnswer::Convergence(())) => unreachable!(),
                    Err(error) => eprintln!("{error}"),
                }
            }
        }
    }
}
