#!/usr/bin/env bash

set -euo pipefail
wd=$(dirname "$0")
# ensure working directory is in artifact folder root
cd $wd

# temporary docker run command that mounts `./results/` and `./figs` on the host in the container
DOCKER_CMD="docker run --rm -ti -v "./results/:/results/" -v "./figs/:/figs/" cav25"

mkdir -p results/
$DOCKER_CMD /bin/bash -c 'dotnet fsi ./scripts/process_results.fsx'


