#!/usr/bin/env bash

INPUT=$1
LOOPS=$2
let SEQLOOPS=$LOOPS-1

SCRIPT_DIR="/tools"
executable="${SCRIPT_DIR}/resharp-solver"

if [[ ("$LOOPS" == 1) ]] ; then
  out=$(${executable} ${INPUT})
else
  out=$(for i in `seq $SEQLOOPS` ; do ${executable} ${INPUT}; done > /dev/null ; ${executable} ${INPUT})
fi

ret=$?
echo "result: ${out}"

exit ${ret}
