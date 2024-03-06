#!/bin/bash

# Copyright 2022-2023 VMware, Inc.
# SPDX-License-Identifier: BSD-2-Clause

# Install dependencies for an EC2 instance running Amazon Linux

set -e

cd

sudo yum -y update
sudo yum -y groupinstall "Development Tools"
sudo yum -y install htop
sudo yum -y install python

# install rustup (-y disables confirmation)
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
# don't try to read this file
# shellcheck disable=SC1091
source "$HOME/.cargo/env"

if [ ! -e ~/temporal-verifier ]; then
  # TODO: remove branch when qalpha is merged
  git clone -b qalpha-simulations https://github.com/vmware-research/temporal-verifier
fi
cd ~/temporal-verifier
./tools/download-solvers.sh

# don't use downloaded z3, it won't work due to an outdated libstd++ in the
# Amazon Linux image
rm solvers/z3

# compile Z3 from source
# takes about 10min on z1d.xlarge
wget 'https://github.com/Z3Prover/z3/archive/refs/tags/z3-4.12.2.tar.gz'
tar -xf z3-4.12.2.tar.gz

cd z3-z3-4.12.2
./configure >/dev/null
cd build
time make -j"$(nproc)"
sudo make install
cd

cargo build --release
cargo build
