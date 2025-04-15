#!/usr/bin/env bash

set -euo pipefail
wd=$(dirname "$0")

cd "$wd/source/resharp-solver"
cargo build --release