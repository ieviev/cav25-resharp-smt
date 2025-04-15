#!/usr/bin/env bash

INPUT=$1
LOOPS=$2
let SEQLOOPS=$LOOPS-1
echo "$SEQLOOPS"

SCRIPT_DIR="/tools"
executable="${SCRIPT_DIR}/cvc5"

if [[ ("$LOOPS" == 1) ]] ; then
  out=$(${executable} --lang smt2 ${INPUT})
else
  out=$(for i in `seq $SEQLOOPS` ; do ${executable} --lang smt2 ${INPUT}; done > /dev/null ; ${executable} --lang smt2 ${INPUT})
fi
ret=$?
echo "result: ${out}"

exit ${ret}
