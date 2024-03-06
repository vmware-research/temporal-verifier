// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Define the qalpha experiments
use itertools::Itertools;
use std::{
    collections::HashMap,
    path::{Path, PathBuf},
    time::Duration,
};

use crate::run::BenchmarkConfig;

/// Return a list of configured qalpha benchmarks for the examples.
///
/// Each benchmark is represented as a tuple of a name and a configuration. The
/// name is used as the output directory so it should be unique across
/// benchmarks.
pub fn qalpha_benchmarks(
    safety_time_limit: Duration,
    fixpoint_time_limit: Duration,
    scalability_time_limit: Duration,
) -> Vec<(PathBuf, BenchmarkConfig)> {
    let configs = vec![
        QalphaConfig {
            file: PathBuf::from("fol/lockserv.fly"),
            quantifiers: "F node 2",
            clause_size: 3,
            cubes: 0,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
            scalability: vec![],
        },
        QalphaConfig {
            file: PathBuf::from("fol/toy_consensus_forall.fly"),
            quantifiers: "F node 1; F value 2",
            clause_size: 3,
            cubes: 0,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
            scalability: vec![],
        },
        QalphaConfig {
            file: PathBuf::from("fol/ring_id.fly"),
            quantifiers: "F node 3",
            clause_size: 3,
            cubes: 0,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
            scalability: vec![],
        },
        QalphaConfig {
            file: PathBuf::from("fol/sharded_kv.fly"),
            quantifiers: "F key 1; F node 2; F value 2",
            clause_size: 3,
            cubes: 0,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
            scalability: vec![],
        },
        QalphaConfig {
            file: PathBuf::from("fol/ticket.fly"),
            quantifiers: "F thread 2; F ticket 2",
            clause_size: 5,
            cubes: 0,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
            scalability: vec![],
        },
        QalphaConfig {
            file: PathBuf::from("fol/learning_switch.fly"),
            quantifiers: "F node 4",
            clause_size: 4,
            cubes: 0,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
            scalability: vec![],
        },
        QalphaConfig {
            file: PathBuf::from("fol/consensus_wo_decide.fly"),
            quantifiers: "F node 3",
            clause_size: 3,
            cubes: 0,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
            scalability: vec![],
        },
        QalphaConfig {
            file: PathBuf::from("fol/consensus_forall.fly"),
            quantifiers: "F node 3; F value 1",
            clause_size: 3,
            cubes: 0,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
            scalability: vec![],
        },
        QalphaConfig {
            file: PathBuf::from("fol/cache.fly"),
            quantifiers: "F address 2; F core 2; F value 2",
            clause_size: 5,
            cubes: 0,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
            scalability: vec![],
        },
        QalphaConfig {
            file: PathBuf::from("fol/sharded_kv_no_lost_keys.fly"),
            quantifiers: "F key 1; * node 1; * value 1",
            clause_size: 2,
            cubes: 0,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
            scalability: vec![],
        },
        QalphaConfig {
            file: PathBuf::from("fol/toy_consensus_epr.fly"),
            quantifiers: "F value 2; * quorum 1; F node 1",
            clause_size: 3,
            cubes: 0,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
            scalability: vec![],
        },
        QalphaConfig {
            file: PathBuf::from("fol/consensus_epr.fly"),
            quantifiers: "* quorum 1; F node 3; F value 1",
            clause_size: 3,
            cubes: 0,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
            scalability: vec![],
        },
        QalphaConfig {
            file: PathBuf::from("fol/client_server_ae.fly"),
            quantifiers: "F node 1; F response 1; * request 1",
            clause_size: 1,
            cubes: 1,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
            scalability: vec![],
        },
        QalphaConfig {
            file: PathBuf::from("fol/paxos_epr.fly"),
            quantifiers: "F round 2; F value 2; * quorum 1; * node 1",
            clause_size: 3,
            cubes: 1,
            nesting: Some(1),
            sim: Default::default(),
            fragment: Fragment::Epr,
            scalability: vec![
                Scalability {
                    quantifiers: "F round 2; F value 2; * quorum 1; * node 1".to_string(),
                    qf: "pdnf".to_string(),
                    clause_size: Some(3),
                    cubes: Some(1),
                    bound: "round=3 value=2 quorum=2 node=2".to_string(),
                },
                Scalability {
                    quantifiers: "F round 2; F value 2; * quorum 1; * node 1".to_string(),
                    qf: "cnf".to_string(),
                    clause_size: Some(4),
                    cubes: None,
                    bound: "round=3 value=2 quorum=2 node=2".to_string(),
                },
                Scalability {
                    quantifiers: "F round 2; F value 2; * quorum 1; * node 1".to_string(),
                    qf: "dnf".to_string(),
                    clause_size: None,
                    cubes: Some(3),
                    bound: "round=3 value=2 quorum=2 node=2".to_string(),
                },
            ],
        },
        QalphaConfig {
            file: PathBuf::from("fol/flexible_paxos_epr.fly"),
            quantifiers: "F round 2; F value 2; * quorum_2 1; * node 1",
            clause_size: 3,
            cubes: 1,
            nesting: Some(1),
            sim: Default::default(),
            fragment: Fragment::Epr,
            scalability: vec![],
        },
        QalphaConfig {
            file: PathBuf::from("fol/multi_paxos_epr.fly"),
            quantifiers: "F inst 1; F round 2; F value 2; * quorum 1; * node 2",
            clause_size: 3,
            cubes: 1,
            nesting: Some(2),
            sim: Default::default(),
            fragment: Fragment::Epr,
            scalability: vec![],
        },
        QalphaConfig {
            file: PathBuf::from("fol/fast_paxos_epr.fly"),
            quantifiers: "F round 2; F value 2; * quorum_c 1; * quorum_f 1; * node 1",
            clause_size: 4,
            cubes: 1,
            nesting: Some(1),
            sim: Default::default(),
            fragment: Fragment::Epr,
            scalability: vec![],
        },
        QalphaConfig {
            file: PathBuf::from("fol/stoppable_paxos_epr.fly"),
            quantifiers: "F inst 2; F votemap 1; F round 2; F value 2; * quorum 1; * node 2",
            clause_size: 5,
            cubes: 1,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
            scalability: vec![],
        },
        QalphaConfig {
            file: PathBuf::from("fol/vertical_paxos_epr.fly"),
            quantifiers: "F round 2; F value 2; * config 1; * quorum 1; * node 1",
            clause_size: 5,
            cubes: 2,
            nesting: Some(2),
            sim: Default::default(),
            fragment: Fragment::Epr,
            scalability: vec![],
        },
        QalphaConfig {
            file: PathBuf::from("fol/bosco_3t_safety.fly"),
            quantifiers: "F value 1; * value 2; * quorum_b 1; * node 2",
            clause_size: 5,
            cubes: 2,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::None,
            scalability: vec![],
        },
        QalphaConfig {
            file: PathBuf::from("fol/firewall.fly"),
            quantifiers: "F node 1; * node 1",
            clause_size: 1,
            cubes: 1,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::None,
            scalability: vec![],
        },
        QalphaConfig {
            file: PathBuf::from("fol/ring_id_not_dead.fly"),
            quantifiers: "* node 2; F node 1; * id 1",
            clause_size: 3,
            cubes: 3,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::None,
            scalability: vec![],
        },
        QalphaConfig {
            file: PathBuf::from("fol/client_server_db_ae.fly"),
            quantifiers: "F db_request_id 1; F node 2; F response 1; * request 1; * node 1",
            clause_size: 3,
            cubes: 1,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::None,
            scalability: vec![],
        },
        QalphaConfig {
            file: PathBuf::from("fol/hybrid_reliable_broadcast_cisa.fly"),
            quantifiers: "* quorum_a 1; F node 1; * quorum_b 1; * node 1",
            clause_size: 4,
            cubes: 2,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::None,
            scalability: vec![],
        },
        QalphaConfig {
            file: PathBuf::from("fol/block_cache_system_frozen_async.fly"),
            quantifiers: "F node 2; F req_id 2; F ref 1; F location 1; * ref 1; * location 1",
            clause_size: 4,
            cubes: 1,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::None,
            scalability: vec![],
        },
    ];

    let benchmarks = named_benchmarks(
        configs,
        safety_time_limit,
        fixpoint_time_limit,
        scalability_time_limit,
    );
    check_unique_benchmarks(&benchmarks);
    benchmarks
}

fn example_path(file: &Path) -> PathBuf {
    PathBuf::from("temporal-verifier/examples").join(file)
}

enum Fragment {
    Epr,
    None,
}

impl ToString for Fragment {
    fn to_string(&self) -> String {
        match self {
            Fragment::Epr => "epr".to_string(),
            Fragment::None => "none".to_string(),
        }
    }
}

struct SortCount {
    sort: String,
    count: usize,
}

#[allow(dead_code)]
enum SimulationBound {
    None,
    Sum(usize),
    Exact(Vec<SortCount>),
}

impl SimulationBound {
    fn params(&self) -> Vec<String> {
        match self {
            SimulationBound::None => vec![],
            SimulationBound::Sum(bound_sum) => vec![format!("--bound-sum={bound_sum}")],
            SimulationBound::Exact(bounds) => bounds
                .iter()
                .flat_map(|SortCount { sort, count }| {
                    ["--bound".to_string(), format!("{sort}={count}")]
                })
                .collect(),
        }
    }
}

struct SimulationConfig {
    bound: SimulationBound,
    depth: Option<usize>,
    guided: bool,
}

impl SimulationConfig {
    fn params(&self) -> Vec<String> {
        let mut params = self.bound.params();
        if let Some(d) = self.depth {
            params.push(format!("--depth={d}"));
        }
        if self.guided {
            params.push("--guided".to_string())
        }
        params
    }
}

impl Default for SimulationConfig {
    fn default() -> Self {
        Self {
            bound: SimulationBound::None,
            depth: None,
            guided: false,
        }
    }
}

struct Scalability {
    quantifiers: String,
    qf: String,
    clause_size: Option<usize>,
    cubes: Option<usize>,
    bound: String,
}

/// A configuration for a run of qalpha
struct QalphaConfig<'a> {
    file: PathBuf,
    quantifiers: &'a str,
    clause_size: usize,
    cubes: usize,
    nesting: Option<usize>,
    sim: SimulationConfig,
    fragment: Fragment,
    scalability: Vec<Scalability>,
}

fn command() -> Vec<String> {
    vec!["infer".to_string(), "qalpha".to_string()]
}

#[allow(dead_code)]
fn sort_counts(spec: &str) -> Vec<SortCount> {
    spec.split(' ')
        .map(|s| {
            let mut parts = s.split('=');
            let sort = parts.next().unwrap();
            let count = parts.next().unwrap().parse().unwrap();
            SortCount {
                sort: sort.to_string(),
                count,
            }
        })
        .collect()
}

fn quantifier_param(spec: &str) -> impl Iterator<Item = String> + '_ {
    spec.split("; ")
        .flat_map(|s| ["--quantifier".to_string(), s.to_string()])
}

impl<'a> QalphaConfig<'a> {
    fn params(&self, sim: &SimulationConfig, strategy: &str, baseline: bool) -> Vec<String> {
        let mut args = vec![];
        args.extend(quantifier_param(self.quantifiers));
        args.push(format!("--clause-size={}", self.clause_size));
        args.push(format!("--cubes={}", self.cubes));
        if let Some(n) = self.nesting {
            args.push(format!("--nesting={n}"));
        }
        args.extend(sim.params());
        args.push(format!("--strategy={strategy}"));
        if baseline {
            args.push("--baseline".to_string());
        }
        args
    }

    fn scalability_benchmarks(
        &self,
        scalability_time_limit: Duration,
    ) -> Vec<(PathBuf, BenchmarkConfig)> {
        self.scalability
            .iter()
            .enumerate()
            .flat_map(|(i, s)| {
                let sim = SimulationBound::Exact(sort_counts(&s.bound));
                let mut params = quantifier_param(&s.quantifiers).collect_vec();
                params.push(format!("--qf={}", s.qf));
                if let Some(cl) = s.clause_size {
                    params.push(format!("--clause-size={cl}"));
                }
                if let Some(cb) = s.cubes {
                    params.push(format!("--cubes={cb}"));
                }
                params.extend(sim.params());
                params.push("--strategy=none".to_string());

                let mut baseline_params = params.clone();
                baseline_params.push("--baseline".to_string());
                [
                    (
                        self.full_path(format!("scalability-{}-{i}", s.qf).as_str()),
                        BenchmarkConfig {
                            command: command(),
                            params,
                            file: example_path(&self.file),
                            time_limit: scalability_time_limit,
                        },
                    ),
                    (
                        self.full_path(format!("scalability-{}-{i}-baseline", s.qf).as_str()),
                        BenchmarkConfig {
                            command: command(),
                            params: baseline_params,
                            file: example_path(&self.file),
                            time_limit: scalability_time_limit,
                        },
                    ),
                ]
            })
            .collect()
    }

    pub fn benchmarks(
        &self,
        safety_time_limit: Duration,
        fixpoint_time_limit: Duration,
        scalability_time_limit: Duration,
    ) -> Vec<(PathBuf, BenchmarkConfig)> {
        let mut benchmarks = self.scalability_benchmarks(scalability_time_limit);
        benchmarks.extend([
            // Safety benchmark (property directed)
            (
                self.full_path("safety"),
                BenchmarkConfig {
                    command: command(),
                    params: self.params(&self.sim, "weaken-pd", false),
                    file: example_path(&self.file),
                    time_limit: safety_time_limit,
                },
            ),
            // Fixpoint benchmark
            (
                self.full_path("fixpoint"),
                BenchmarkConfig {
                    command: command(),
                    params: self.params(&self.sim, "weaken", false),
                    file: example_path(&self.file),
                    time_limit: fixpoint_time_limit,
                },
            ),
            // Fixpoint benchmark with baseline datastructure
            (
                self.full_path("fixpoint-baseline"),
                BenchmarkConfig {
                    command: command(),
                    params: self.params(&self.sim, "weaken", true),
                    file: example_path(&self.file),
                    time_limit: fixpoint_time_limit,
                },
            ),
        ]);
        benchmarks
    }

    /// Give this benchmark a systematic path that includes enough information
    /// to (hopefully) make it unique.
    fn full_path(&self, sub_name: &str) -> PathBuf {
        PathBuf::from(format!(
            "{}/{}-{sub_name}",
            self.file.display(),
            self.fragment.to_string(),
        ))
    }
}

/// Convert a list of QalphaConfig to benchmarks with systematic names.
///
/// Automatically names multiple configurations for the same fly file using
/// [`QalphaConfig::full_path`].
fn named_benchmarks(
    configs: Vec<QalphaConfig>,
    safety_time_limit: Duration,
    fixpoint_time_limit: Duration,
    scalability_time_limit: Duration,
) -> Vec<(PathBuf, BenchmarkConfig)> {
    configs
        .into_iter()
        .flat_map(|config| {
            config.benchmarks(
                safety_time_limit,
                fixpoint_time_limit,
                scalability_time_limit,
            )
        })
        .collect()
}

/// Check that the names for all the benchmarks are unique (to avoid results
/// from one benchmark overriding an earlier one).
fn check_unique_benchmarks(benchmarks: &[(PathBuf, BenchmarkConfig)]) {
    let mut by_name: HashMap<&Path, Vec<BenchmarkConfig>> = HashMap::new();
    for (name, config) in benchmarks {
        by_name.entry(name).or_default().push(config.clone());
    }
    for (name, configs) in by_name {
        if configs.len() > 1 {
            panic!(
                "benchmark name {} is not unique: {configs:?}",
                name.display()
            );
        }
    }
}
