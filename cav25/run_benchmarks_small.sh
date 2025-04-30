#!/usr/bin/env bash

set -euo pipefail
wd=$(dirname "$0")
# ensure working directory is in artifact folder root
cd $wd

# temporary docker run command that mounts `./results/` on the host in the container
DOCKER_CMD="docker run --rm -ti -v "./results/:/results/" cav25"

# available: 
# sygus_qgen denghang automatark boolean_and_loops date det_blowup password regexlib_membership regexlib_intersection regexlib_subset state_space singlefile

BENCHMARKS="boolean_and_loops date password"

mkdir -p results/
$DOCKER_CMD /bin/bash -c "/run_bench.sh -t resharp-solver $BENCHMARKS"
$DOCKER_CMD /bin/bash -c "/run_bench.sh -t z3-noodler $BENCHMARKS"
$DOCKER_CMD /bin/bash -c "/run_bench.sh -t cvc5 $BENCHMARKS"
$DOCKER_CMD /bin/bash -c "/run_bench.sh -t z3 $BENCHMARKS"
$DOCKER_CMD /bin/bash -c "/run_bench.sh -t z3str3 $BENCHMARKS"
$DOCKER_CMD /bin/bash -c "/run_bench.sh -t z3str4 $BENCHMARKS"
$DOCKER_CMD /bin/bash -c "/run_bench.sh -t ostrich $BENCHMARKS"
$DOCKER_CMD /bin/bash -c "/run_bench.sh -t ostrichrecl $BENCHMARKS"
$DOCKER_CMD /bin/bash -c "/run_bench.sh -t z3alpha $BENCHMARKS"
