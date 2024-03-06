// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Advanced parallelism infrastructure

use crate::hashmap::{HashMap, HashSet};
use std::collections::BTreeMap;
use std::hash::Hash;
use std::sync::Mutex;

use std::thread;
use std::time::Duration;

/// A set of tasks for parallel execution, ordered by priority.
pub struct Tasks<P: Ord + Clone, T: Eq + Hash> {
    tasks: BTreeMap<P, HashSet<T>>,
    total_inserted: usize,
}

impl<P: Ord + Clone, T: Eq + Hash> Tasks<P, T> {
    /// Create an empty set of tasks.
    pub fn new() -> Self {
        Self {
            tasks: BTreeMap::new(),
            total_inserted: 0,
        }
    }

    /// Return the number of remaining tasks.
    pub fn len(&self) -> usize {
        self.tasks.values().map(|v| v.len()).sum()
    }

    /// Return whether there are no tasks remaining.
    pub fn is_empty(&self) -> bool {
        self.tasks.is_empty()
    }

    // Return the total number of tasks inserted.
    pub fn total(&self) -> usize {
        self.total_inserted
    }

    /// Insert a new task with the given priority.
    pub fn insert(&mut self, priority: P, task: T) {
        self.total_inserted += 1;
        if let Some(ts) = self.tasks.get_mut(&priority) {
            ts.insert(task);
        } else {
            self.tasks.insert(priority, HashSet::from_iter([task]));
        }
    }

    /// Get a highest-priority task.
    fn pop(&mut self) -> Option<(P, T)> {
        if let Some(p) = self.tasks.first_key_value().map(|(p, _)| p.clone()) {
            let p_tasks = self.tasks.get_mut(&p).unwrap();
            let t = p_tasks.pop().unwrap();
            if p_tasks.is_empty() {
                self.tasks.remove(&p);
            }
            Some((p, t))
        } else {
            None
        }
    }
}

impl<P: Ord + Clone, T: Eq + Hash> FromIterator<(P, T)> for Tasks<P, T> {
    fn from_iter<I: IntoIterator<Item = (P, T)>>(iter: I) -> Self {
        let mut tasks = Self::new();
        iter.into_iter().for_each(|(p, t)| tasks.insert(p, t));
        tasks
    }
}

/// A manager for prioritized tasks to be executed in parallel.
struct ParallelExecution<'a, P, T, R>
where
    P: Ord + Clone,
    T: Eq + Hash,
{
    /// The tasks to be performed.
    tasks: &'a mut Tasks<P, T>,
    /// Running tasks.
    running: HashSet<T>,
    /// Finished tasks and their result.
    results: HashMap<T, R>,
    /// Number of tasks currently being processed.
    processing: usize,
    /// Whether this batch of tasks has been canceled.
    cancel: bool,
}

impl<'a, P, T, R> ParallelExecution<'a, P, T, R>
where
    P: Ord + Clone,
    T: Eq + Hash + Clone,
{
    /// Gets a highest-priority task that wasn't seen yet, if processing power is available.
    /// This also increments the processing count.
    fn get_task(&mut self) -> Option<(P, T)> {
        if !self.cancel {
            while let Some((p, t)) = self.tasks.pop() {
                if self.unseen(&t) {
                    self.processing += 1;
                    self.running.insert(t.clone());
                    return Some((p, t));
                }
            }
        }

        None
    }

    /// Handle a result to a task.
    /// This also deducts one from the processing count, and returns the number of workers that should be launched next.
    fn handle_result(&mut self, task: T, res: TaskResult<P, T, R>) {
        self.processing -= 1;
        self.running.remove(&task);
        let (result, new_tasks, cancel) = res;
        self.results.insert(task, result);
        for (new_p, new_t) in new_tasks {
            self.tasks.insert(new_p, new_t)
        }

        self.cancel |= cancel;
    }

    /// Check whether the given task has been seen (started or executed) yet.
    fn unseen(&self, task: &T) -> bool {
        !self.running.contains(task) && !self.results.contains_key(task)
    }
}

/// The result of a task, consisting of a results type, a vector of new tasks
/// to add to the workload, as well as a `bool` determining whether to cancel (if `true`)
/// the current exection of tasks (by not launching new ones).
type TaskResult<P, T, R> = (R, Vec<(P, T)>, bool);

/// Available parallelism.
pub fn parallelism() -> usize {
    std::thread::available_parallelism().unwrap().get()
}

/// A worker able to execute prioritized tasks in parallel.
/// The work closure gets a reference to a taks and its priority,
/// and returns a result in the form of a [`TaskResult`].
pub struct ParallelWorker<'a, P, T, R, F>
where
    P: Ord + Clone + Send + Sync,
    T: Clone + Eq + Hash + Send + Sync,
    R: Send + Sync,
    F: Fn(&P, &T) -> TaskResult<P, T, R> + Send + Sync,
{
    exec: Mutex<ParallelExecution<'a, P, T, R>>,
    work: F,
}

impl<'a, P, T, R, F> ParallelWorker<'a, P, T, R, F>
where
    P: Ord + Clone + Send + Sync,
    T: Clone + Eq + Hash + Send + Sync,
    R: Send + Sync,
    F: Fn(&P, &T) -> TaskResult<P, T, R> + Send + Sync,
{
    /// Create a new worker with the given tasks and work closure.
    pub fn new(tasks: &'a mut Tasks<P, T>, work: F) -> Self {
        let exec = Mutex::new(ParallelExecution {
            tasks,
            running: HashSet::default(),
            results: HashMap::default(),
            processing: 0,
            cancel: false,
        });

        Self { exec, work }
    }

    /// Run the worker and perform tasks in parallel.
    pub fn run(self, num_workers: usize) -> HashMap<T, R> {
        thread::scope(|s| {
            for _ in 0..num_workers {
                s.spawn(|| self.worker());
            }
        });

        let exec = self.exec.into_inner().unwrap();
        exec.results
    }

    /// Run a single-threaded worker which gets the next task and performs it.
    fn worker(&self) {
        loop {
            let task;
            {
                let mut exec = self.exec.lock().unwrap();
                task = exec.get_task();
                if task.is_none() && (exec.cancel || exec.processing == 0) {
                    return;
                }
            }

            if let Some((p, t)) = task {
                let res: TaskResult<P, T, R> = (self.work)(&p, &t);
                {
                    let mut exec = self.exec.lock().unwrap();
                    exec.handle_result(t, res);
                }
            } else {
                thread::sleep(Duration::from_millis(1));
            }
        }
    }
}
