#!/usr/bin/env bash

# this script runs ./run_bench_singlerun.sh inside the container 
# and outputs the results to ./result
# pass --help for options

set -euo pipefail
wd=$(dirname "$0")
# ensure working directory is in artifact folder root
cd $wd

# temporary docker run command that mounts `./results/` on the host in the container
DOCKER_CMD="docker run --rm -ti -v "./results/:/results/" cav25"

args="$*"
$DOCKER_CMD /bin/bash -c "/run_bench_singlerun.sh $args"


