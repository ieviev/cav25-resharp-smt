#!/usr/bin/env bash

set -euo pipefail
wd=$(dirname "$0")

cd "$wd/source/resharp-solver"
# cargo run --release --features testing
cargo run --release --features testing --features count_derivatives
