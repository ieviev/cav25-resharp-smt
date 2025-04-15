#!/usr/bin/env bash

set -euo pipefail
wd=$(dirname "$0")
# ensure working directory is in artifact folder root
cd $wd

DOCKER_CMD="docker run --rm -ti -v "./results/:/results/" -v "./figs/:/figs/" cav25"

# run bash inside the shell
echo "---------------------------------"
echo "-- interactive shell --"
echo "-- try ./run_bench_singlerun.sh --help or see the tools used in their respective directories --"
$DOCKER_CMD /bin/bash 


