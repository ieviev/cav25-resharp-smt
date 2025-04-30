#!/usr/bin/env bash

set -euo pipefail
wd=$(dirname "$0")
# ensure working directory is in artifact folder root
cd $wd

# temporary docker run command that mounts `./results/` on the host in the container
DOCKER_CMD="docker run --rm -ti -v "./results/:/results/" cav25"

mkdir -p results/
$DOCKER_CMD /bin/bash -c '/run_bench_with_repetitions.sh sygus_qgen denghang automatark boolean_and_loops date det_blowup password regexlib_membership regexlib_intersection regexlib_subset state_space'


