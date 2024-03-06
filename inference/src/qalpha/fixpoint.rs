// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Find a fixpoint invariant expressing reachable states in a given
//! lemma domain.

use fly::semantics::Model;
use solver::basics::{BasicCanceler, MultiCanceler};
use std::cmp::Ordering;
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

use crate::{
    basics::{FOModule, QalphaConfig, QfBody, SimulationConfig},
    parallel::parallelism,
    parallel::Tasks,
    qalpha::{
        atoms::generate_literals,
        frame::{InductionFrame, OperationStats},
        language::{advanced, baseline, BoundedLanguage},
    },
};
use fly::syntax::{BinOp, Module, Term, ThmStmt};
use solver::{
    backends::SolverType,
    basics::{BasicSolver, FallbackSolvers, ParallelSolvers},
    conf::SolverConf,
};

use rayon::prelude::*;

macro_rules! timed {
    ($blk:block) => {{
        let start = Instant::now();
        $blk
        start.elapsed()
    }};
}

pub mod defaults {
    pub const QUANT_SAME_SORT: usize = 3;
    pub const SIMULATION_SORT_SIZE: usize = 0;
    pub const MIN_DISJUNCTS: usize = 2;
    pub const MIN_NON_UNIT_SIZE: usize = 2;
}

#[derive(PartialEq, Eq, Clone)]
pub enum TraversalDepth {
    Bfs(usize),
    Dfs(usize),
}

use TraversalDepth::*;

impl TraversalDepth {
    pub fn depth(&self) -> usize {
        match self {
            TraversalDepth::Bfs(d) | TraversalDepth::Dfs(d) => *d,
        }
    }
}

impl PartialOrd for TraversalDepth {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TraversalDepth {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Bfs(x), Bfs(y)) => x.cmp(y),
            (Dfs(x), Dfs(y)) => x.cmp(y).reverse(),
            _ => panic!("cannot compare BFS and DFS depths!"),
        }
    }
}

/// (sum of universe sizes, simulation depth)
pub type SamplePriority = (usize, TraversalDepth);

pub fn sample_priority(
    cfg: &SimulationConfig,
    universe: &[usize],
    depth: usize,
) -> Option<SamplePriority> {
    let sum: usize = universe.iter().product();
    if !cfg.depth.is_some_and(|d| depth > d) {
        Some((sum, if cfg.dfs { Dfs(depth) } else { Bfs(depth) }))
    } else {
        None
    }
}

pub enum Strategy {
    None,
    Houdini,
    HoudiniPd,
    Weaken,
    WeakenPd,
}

impl Default for Strategy {
    fn default() -> Self {
        Self::Weaken
    }
}

impl From<&String> for Strategy {
    fn from(value: &String) -> Self {
        match value.as_str() {
            "none" => Self::None,
            "houdini" => Self::Houdini,
            "houdini-pd" => Self::HoudiniPd,
            "weaken" => Self::Weaken,
            "weaken-pd" => Self::WeakenPd,
            _ => panic!("invalid CTI option"),
        }
    }
}

impl Strategy {
    fn property_directed(&self) -> bool {
        matches!(self, Self::HoudiniPd | Self::WeakenPd)
    }

    fn is_weaken(&self) -> bool {
        matches!(self, Self::Weaken | Self::WeakenPd)
    }

    fn is_houdini(&self) -> bool {
        matches!(self, Self::Houdini | Self::HoudiniPd)
    }
}

/// Check how much of the handwritten invariant the given lemmas cover.
fn invariant_cover<S: BasicSolver>(
    m: &Module,
    solver: &S,
    fo: &FOModule,
    lemmas: &[Term],
) -> (usize, usize) {
    let proof = m
        .statements
        .iter()
        .filter_map(|s| match s {
            ThmStmt::Assert(p) => Some(p),
            _ => None,
        })
        .next()
        .unwrap();

    let covered = proof
        .invariants
        .par_iter()
        .filter(|inv| {
            !fo.implication_cex(solver, lemmas, &inv.x, None, false)
                .is_cex()
        })
        .count();

    (covered, proof.invariants.len())
}

/// An inductive fixpoint
struct FoundFixpoint {
    /// The last frame of the fixpoint computation.
    /// This is inductive iff `reduced_proof` is not `None`
    proof: Vec<Term>,
    /// The fixpoint term, semantically reduced.
    /// If `None`, the run has been terminated/aborted before reaching the fixpoint
    reduced_proof: Option<Vec<Term>>,
    /// A subset of the (reduced) fixpoint term which suffices to prove safety.
    /// If None, the last frame is unsafe
    safety_proof: Option<Vec<Term>>,
    /// Statistics for this execution
    stats: FixpointStats,
}

impl FoundFixpoint {
    #[allow(clippy::too_many_arguments)]
    fn new(
        time: Duration,
        success: bool,
        proof: Vec<Term>,
        full_size: usize,
        max_size: usize,
        reduced_proof: Option<Vec<Term>>,
        safety_proof: Option<Vec<Term>>,
        covering: Option<(usize, usize)>,
        processed_states: usize,
        generated_states: usize,
        weaken_stats: OperationStats,
        get_unsat_stats: OperationStats,
    ) -> Self {
        let stats = FixpointStats {
            time_sec: time.as_secs_f64(),
            success,
            simplified_size: proof.len(),
            full_size,
            max_size,
            reduced: reduced_proof.as_ref().map(|r| r.len()),
            safety: safety_proof.as_ref().map(|r| r.len()),
            covering,
            processed_states,
            generated_states,
            weaken_stats,
            get_unsat_stats,
        };
        FoundFixpoint {
            proof,
            reduced_proof,
            safety_proof,
            stats,
        }
    }

    fn report(&self, print_nondet: bool) {
        let print_inv = |name: &str, size: usize, inv: &[Term]| {
            println!("{name} (size={size}) {{");
            for lemma in inv {
                println!("  invariant {lemma}");
            }
            println!("}} end of {name}");
        };

        if let Some(reduced_proof) = &self.reduced_proof {
            println!(
                "Fixpoint REACHED! frame_size={}, reduced_size={}",
                self.proof.len(),
                reduced_proof.len()
            );
        } else {
            println!("Fixpoint NOT reached! frame_size={}", self.proof.len());
        }

        if let Some(safety_proof) = &self.safety_proof {
            println!("Safety VERIFIED! proof_size={}", safety_proof.len());
        } else {
            println!("Safety NOT verified.");
        }

        if print_nondet {
            print_inv("frame", self.proof.len(), &self.proof);
            if let Some(reduced_proof) = &self.reduced_proof {
                print_inv("reduced", reduced_proof.len(), reduced_proof);
            }
            if let Some(safety_proof) = &self.safety_proof {
                print_inv("safety", safety_proof.len(), safety_proof);
            }

            println!("=============== JSON ===============");
            println!("{}", serde_json::to_string(&self.stats).unwrap());
        }
    }
}

#[derive(serde::Serialize)]
struct FixpointStats {
    /// Total runtime
    time_sec: f64,
    /// Whether the task finished successfully
    success: bool,
    /// The number of formulas in the simplified final frame
    simplified_size: usize,
    /// The number of formulas in the final weaken frame, containing unsimplified formulas
    full_size: usize,
    /// The maximal number of formulas encountered in the weaken frame,
    max_size: usize,
    /// The number of formulas in reduced by implication checks (if available)
    reduced: Option<usize>,
    /// The number of formulas in the safety proof (if available)
    safety: Option<usize>,
    /// Number of lemmas in the handwritten invariant covered by the result
    /// and the total number of lemmas in the handwritten invariants
    covering: Option<(usize, usize)>,
    /// The number of states processed during the execution
    processed_states: usize,
    /// The number of states generated during the execution (some might not have been processed)
    generated_states: usize,
    /// Statistics regarding frame weaken operations
    weaken_stats: OperationStats,
    /// Statistics regarding frame get_unsat operations
    get_unsat_stats: OperationStats,
}

fn parallel_solver(cfg: &QalphaConfig, seeds: usize) -> impl BasicSolver {
    ParallelSolvers::new(
        (0..seeds)
            .flat_map(|seed| {
                [
                    SolverConf::new(SolverType::Z3, true, &cfg.fname, 0, seed),
                    SolverConf::new(SolverType::Cvc5, true, &cfg.fname, 0, seed),
                ]
            })
            .collect(),
    )
}

#[allow(dead_code)]
fn fallback_solver(cfg: &QalphaConfig) -> impl BasicSolver {
    // For the solvers in fallback fashion we alternate between Z3 and CVC5
    // with increasing timeouts and varying seeds, ending with a Z3 solver with
    // no timeout. The idea is to try both Z3 and CVC5 with some timeout to see if any
    // of them solve the query, and gradually increase the timeout for both,
    // ending with no timeout at all. The seed changes are meant to add some
    // variation vis-a-vis previous attempts.
    FallbackSolvers::new(vec![
        SolverConf::new(SolverType::Z3, true, &cfg.fname, 3, 0),
        SolverConf::new(SolverType::Cvc5, true, &cfg.fname, 3, 0),
        SolverConf::new(SolverType::Z3, true, &cfg.fname, 60, 1),
        SolverConf::new(SolverType::Cvc5, true, &cfg.fname, 60, 1),
        SolverConf::new(SolverType::Z3, true, &cfg.fname, 600, 2),
        SolverConf::new(SolverType::Cvc5, true, &cfg.fname, 600, 2),
        SolverConf::new(SolverType::Z3, true, &cfg.fname, 0, 3),
    ])
}

pub fn qalpha<L, S>(
    cfg: Arc<QalphaConfig>,
    lang: Arc<L>,
    m: &Module,
    solver: &S,
    print_nondet: bool,
) where
    L: BoundedLanguage,
    S: BasicSolver,
{
    println!("Running qalpha algorithm...");
    let log_domain_size = lang.log_size();
    println!("Approximate domain size: 10^{log_domain_size:.2}");

    let fixpoint = run_qalpha::<L, S>(cfg.clone(), lang, solver, m, &cfg.fo);
    fixpoint.report(print_nondet);
}

pub fn qalpha_dynamic(cfg: Arc<QalphaConfig>, m: &Module, print_nondet: bool) {
    // TODO: add fallback solver option or remove it from command arguments
    let solver = parallel_solver(&cfg, cfg.seeds);

    // TODO: make nesting and include_eq configurable or remove them from command arguments
    println!("Generating literals...");
    let mut literals: Vec<_>;
    let cube_literals: Vec<_>;
    let gen_time = timed!({
        literals = generate_literals(
            &m.signature,
            &cfg.quant_cfg,
            cfg.qf_cfg.nesting,
            true,
            &cfg.fo,
            &solver,
        );
        let non_universal_vars = cfg.quant_cfg.vars_after_first_exist();
        cube_literals = literals
            .iter()
            .filter(|literal| !literal.ids().is_disjoint(&non_universal_vars))
            .cloned()
            .collect();
        let universal_vars = cfg.quant_cfg.strictly_universal_vars();
        literals.retain(|lit| match (lit.0.as_ref(), lit.1) {
            (Term::BinOp(BinOp::Equals, t1, t2), false) => match (t1.as_ref(), t2.as_ref()) {
                (Term::Id(name1), Term::Id(name2)) => {
                    !universal_vars.contains(name1) && !universal_vars.contains(name2)
                }
                (Term::Id(name), _) | (_, Term::Id(name)) => !universal_vars.contains(name),
                _ => true,
            },
            _ => true,
        });
    });

    println!(
        "Generated {} literals in {}ms ({} containing variables after first existential)",
        literals.len(),
        if print_nondet {
            gen_time.as_millis()
        } else {
            0
        },
        cube_literals.len()
    );

    match (&cfg.qf_cfg.qf_body, cfg.baseline) {
        (QfBody::Cnf, true) => qalpha(
            cfg.clone(),
            baseline::quant_cnf_language(
                cfg.quant_cfg.clone(),
                cfg.qf_cfg.clause_size.unwrap(),
                literals,
            ),
            m,
            &solver,
            print_nondet,
        ),
        (QfBody::Cnf, false) => qalpha(
            cfg.clone(),
            advanced::quant_cnf_language(
                cfg.quant_cfg.clone(),
                cfg.qf_cfg.clause_size.unwrap(),
                literals,
            ),
            m,
            &solver,
            print_nondet,
        ),
        (QfBody::PDnf, true) => qalpha(
            cfg.clone(),
            baseline::quant_pdnf_language(
                cfg.quant_cfg.clone(),
                cfg.qf_cfg.clause_size.unwrap(),
                cfg.qf_cfg.cubes.unwrap(),
                literals,
                cube_literals,
            ),
            m,
            &solver,
            print_nondet,
        ),
        (QfBody::PDnf, false) => qalpha(
            cfg.clone(),
            advanced::quant_pdnf_language(
                cfg.quant_cfg.clone(),
                cfg.qf_cfg.clause_size.unwrap(),
                cfg.qf_cfg.cubes.unwrap(),
                literals,
                cube_literals,
            ),
            m,
            &solver,
            print_nondet,
        ),
        (QfBody::Dnf, true) => qalpha(
            cfg.clone(),
            baseline::quant_dnf_language(
                cfg.quant_cfg.clone(),
                cfg.qf_cfg.cubes.unwrap(),
                literals,
            ),
            m,
            &solver,
            print_nondet,
        ),
        (QfBody::Dnf, false) => qalpha(
            cfg.clone(),
            advanced::quant_dnf_language(
                cfg.quant_cfg.clone(),
                cfg.qf_cfg.cubes.unwrap(),
                literals,
            ),
            m,
            &solver,
            print_nondet,
        ),
    }
}

/// Run the qalpha algorithm on the configured lemma domains.
fn run_qalpha<L, S>(
    cfg: Arc<QalphaConfig>,
    lang: Arc<L>,
    solver: &S,
    m: &Module,
    fo: &FOModule,
) -> FoundFixpoint
where
    L: BoundedLanguage,
    S: BasicSolver,
{
    let start = std::time::Instant::now();

    let mut frame: InductionFrame<L> = InductionFrame::new(
        m,
        m.signature.clone(),
        lang,
        cfg.sim.clone(),
        cfg.strategy.property_directed(),
        parallelism() / (2 * cfg.seeds),
    );

    // Initialize simulations.
    let mut samples: Tasks<SamplePriority, Model> = frame.initial_samples();
    let mut full_houdini_frame: Option<Vec<Term>> = None;

    // Overapproximate initial states.
    if cfg.strategy.is_weaken() {
        loop {
            let ctis = frame.init_cex(fo, solver);
            if ctis.is_empty() {
                break;
            }
            frame.weaken(&ctis);
            for cex in ctis {
                frame.see(&cex);
                samples.insert(sample_priority(&cfg.sim, &cex.universe, 0).unwrap(), cex);
            }
        }

        frame.finish_initial();
    }

    // Handle transition CTI's.
    let mut run_sim = !samples.is_empty();
    let mut run_smt = cfg.strategy.is_weaken() || (cfg.strategy.is_houdini() && !run_sim);
    while run_sim || run_smt {
        let mut ctis: Vec<Model> = vec![];
        let canceler = MultiCanceler::new();
        // Get new samples and CTI's, and if enabled, check the safety of the frame.
        let not_safe = thread::scope(|s| {
            let smt_handle = s.spawn(|| {
                if run_smt {
                    qalpha_cti(&cfg, solver, fo, &frame, canceler.clone())
                } else {
                    Some(vec![])
                }
            });

            ctis = if run_sim {
                frame.extend(&mut samples, canceler.clone())
            } else {
                vec![]
            };

            let smt_cti = smt_handle.join().unwrap();
            // Abort
            if smt_cti.is_none() {
                return true;
            }

            let smt_cti = smt_cti.unwrap();
            for cex in &smt_cti {
                if !matches!(frame.see(cex), Some(false)) {
                    samples.insert(
                        sample_priority(&cfg.sim, &cex.universe, 0).unwrap(),
                        cex.clone(),
                    );
                }
            }
            ctis.extend(smt_cti);

            false
        });

        if not_safe {
            return FoundFixpoint::new(
                start.elapsed(),
                false,
                frame.proof(),
                frame.weaken_lemmas.len(),
                frame.weaken_lemmas.max_size,
                None,
                None,
                None,
                samples.total() - samples.len(),
                samples.total(),
                frame.weaken_stats(),
                frame.get_unsat_stats(),
            );
        }

        if run_sim {
            frame.log_info(format!(
                "{} samples remaining (out of {})",
                samples.len(),
                samples.total()
            ));
        }

        if cfg.strategy.is_houdini() && run_smt {
            frame.remove_unsat(&ctis);
        } else {
            frame.weaken(&ctis);
        }

        run_sim = !ctis.is_empty() && !samples.is_empty();
        run_smt = if cfg.strategy.is_weaken() {
            !ctis.is_empty()
        } else if cfg.strategy.is_houdini() {
            if !run_smt && ctis.is_empty() {
                full_houdini_frame = Some(frame.proof());
            }

            (!run_smt && ctis.is_empty()) || (run_smt && !ctis.is_empty())
        } else {
            false
        }
    }

    if !matches!(cfg.strategy, Strategy::None) {
        frame.log_info("Checking safety...");
        frame.is_safe(fo, solver, None);
    }
    let time = start.elapsed();
    let proof = if cfg.strategy.is_houdini() {
        full_houdini_frame.unwrap()
    } else {
        frame.proof()
    };
    let reduced_proof = frame.reduced_proof();
    let safety_proof = frame.safety_proof();
    let covering = reduced_proof
        .as_ref()
        .map(|reduced| invariant_cover(m, solver, fo, reduced));
    let success = match cfg.strategy {
        Strategy::None => true,
        Strategy::Houdini => reduced_proof.is_some(),
        Strategy::HoudiniPd => safety_proof.is_some(),
        Strategy::Weaken => reduced_proof.is_some(),
        Strategy::WeakenPd => safety_proof.is_some(),
    };

    FoundFixpoint::new(
        time,
        success,
        proof,
        frame.weaken_lemmas.len(),
        frame.weaken_lemmas.max_size,
        reduced_proof,
        safety_proof,
        covering,
        samples.total() - samples.len(),
        samples.total(),
        frame.weaken_stats(),
        frame.get_unsat_stats(),
    )
}

/// Attempt to find a transition CTI for the current frame. If enabled by the configuration, this also checks
/// the safety of the frame and returns `None` if the execution should abort. Otherwise, `Some(_)` is returned
/// which contains a vector of counterexamples.
fn qalpha_cti<L, S>(
    cfg: &QalphaConfig,
    solver: &S,
    fo: &FOModule,
    frame: &InductionFrame<'_, L>,
    canceler: MultiCanceler<MultiCanceler<S::Canceler>>,
) -> Option<Vec<Model>>
where
    L: BoundedLanguage,
    S: BasicSolver,
{
    if canceler.is_canceled() {
        return Some(vec![]);
    }

    if cfg.strategy.property_directed() {
        frame.log_info("Checking safety...");
        match frame.is_safe(fo, solver, Some(canceler.clone())) {
            None => return Some(vec![]),
            Some(false) => {
                canceler.cancel();
                return None;
            }
            Some(true) => frame.log_info("Safety verified."),
        }
    }

    Some(frame.trans_cex(fo, solver, canceler))
}
