#!/usr/bin/env bash

INPUT=$*

SCRIPT_DIR="/tools"

executable="/bench/source/resharp-solver/target/release/resharp-solver"
out=$("$executable" ${INPUT})

ret=$?
echo "result: ${out}"

exit ${ret}
