// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use clap::Parser;
use temporal_verifier::{timing, App};

fn main() {
    pretty_env_logger::init();
    let app = App::parse();
    timing::TIMES.init();
    app.exec();
}
