#!/usr/bin/env bash

set -euo pipefail
wd=$(dirname "$0")
# ensure working directory is in artifact folder root
cd $wd

# temporary docker run command that mounts `./formulae/` on the host in the container
DOCKER_CMD="docker run --rm -ti -v "./formulae/:/outdir/" cav25"

echo "export the smt benchmarks from the container to ./formulae (y/n)?"
read -r is_ok

if [ "$is_ok" != "y" ]; then
    echo "skipping export"
    exit 0
fi

echo "exporting..."
$DOCKER_CMD /bin/bash -c 'cp -a -rv /formulae/* /outdir/ && chmod -R +rw /outdir/'
echo "done!"
echo "note: to change the permissions of the docker folder on linux run 'sudo chown -R \$USER ./formulae'"
