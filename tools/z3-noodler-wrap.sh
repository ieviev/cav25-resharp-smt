#!/usr/bin/env bash

INPUT=$1
LOOPS=$2
let SEQLOOPS=$LOOPS-1
echo "$SEQLOOPS"

SCRIPT_DIR="/tools"
executable="${SCRIPT_DIR}/z3-noodler"

if [[ ("$LOOPS" == 1) ]] ; then
  out=$(${executable} smt.string_solver="noodler" -smt2 ${INPUT})
else
  out=$(for i in `seq $SEQLOOPS` ;  do ${executable} smt.string_solver="noodler" -smt2 ${INPUT} ; done > /dev/null ; ${executable} smt.string_solver="noodler" -smt2 ${INPUT})
fi

ret=$?
echo "result: ${out}"

exit ${ret}
