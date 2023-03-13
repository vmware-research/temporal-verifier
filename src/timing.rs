// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use std::{
    sync::Mutex,
    time::{Duration, Instant},
};

use itertools::Itertools;
use lazy_static::lazy_static;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum TimeType {
    CheckSatCall { sat: bool },
    GetModel,
    GetMinimalModel,
}

impl TimeType {
    fn name(&self) -> &'static str {
        match self {
            TimeType::CheckSatCall { sat: false } => "check-sat (unsat)",
            TimeType::CheckSatCall { sat: true } => "check-sat (sat)",
            TimeType::GetModel => "get-model",
            TimeType::GetMinimalModel => "get-minimal-model",
        }
    }
}

/// A single timing event.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct TimeInfo {
    typ: TimeType,
    dur: Duration,
}

#[derive(Clone, Debug)]
struct TimingVec {
    times: Vec<TimeInfo>,
}

/// A record of timing measurements.
///
/// `Sync` to support concurrent time recording.
pub struct Timings(Mutex<TimingVec>, Instant);

impl Timings {
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Timings(Mutex::new(TimingVec { times: vec![] }), Instant::now())
    }

    /// Hack to make sure start time is initialized
    pub fn init(&self) {}

    fn record_duration(&self, typ: TimeType, dur: Duration) {
        let mut times = self.0.lock().unwrap();
        times.times.push(TimeInfo { typ, dur })
    }

    /// Record a timing elapsed since `start`.
    pub fn elapsed(&self, typ: TimeType, start: Instant) {
        let dur = start.elapsed();
        self.record_duration(typ, dur);
    }

    /// Print a full timing report to stdout.
    pub fn report(&self) {
        if cfg!(debug_assertions) {
            eprintln!("warning: this is a debug build, non-solver time will be worse");
        }
        let total_time = self.1.elapsed().as_secs_f64();
        println!("{:<22}: {total_time:.1}s", "total");

        let times = {
            let times = self.0.lock().unwrap();
            times.times.clone()
        };
        let count = times.len();
        let solver_total = times
            .iter()
            .map(|info| info.dur)
            .sum::<Duration>()
            .as_secs_f64();
        println!("  {:<20}: {:.1}s", "non-solver", total_time - solver_total);
        println!(
            "  {:<20}: {solver_total:.1}s {count:>4} calls",
            "solver total",
        );

        let totals = times
            .iter()
            .into_grouping_map_by(|info| info.typ)
            .fold((Duration::ZERO, 0), |(dur, count), _key, t| {
                (dur + t.dur, count + 1)
            });
        for typ in [
            TimeType::CheckSatCall { sat: false },
            TimeType::CheckSatCall { sat: true },
            TimeType::GetModel,
            TimeType::GetMinimalModel,
        ] {
            let (time, count) = totals.get(&typ).unwrap_or(&(Duration::ZERO, 0));
            if *count > 0 {
                println!(
                    "    {:<18}: {:.1}s {count:>4} calls ",
                    typ.name(),
                    time.as_secs_f64()
                );
            }
        }
    }
}

lazy_static! {
    pub static ref TIMES: Timings = Timings::new();
}

pub fn start() -> Instant {
    Instant::now()
}

pub fn elapsed(typ: TimeType, start: Instant) {
    TIMES.elapsed(typ, start)
}

pub fn report() {
    TIMES.report()
}
