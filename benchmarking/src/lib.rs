// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Tools for benchmarking flyvy on the examples.

#![deny(missing_docs)]
// configure clippy
#![deny(clippy::uninlined_format_args)]
#![allow(clippy::comparison_to_empty)]
// documentation-related lints (only checked when running rustdoc)
#![allow(rustdoc::private_intra_doc_links)]
#![deny(rustdoc::broken_intra_doc_links)]

pub mod measurement;
pub mod qalpha;
pub mod report;
pub mod run;
pub mod time_bench;
