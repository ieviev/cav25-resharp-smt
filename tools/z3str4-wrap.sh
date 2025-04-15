#!/usr/bin/env bash

INPUT=$1
LOOPS=$2
let SEQLOOPS=$LOOPS-1

SCRIPT_DIR="/tools"
executable="${SCRIPT_DIR}/z3str4"

if [[ ("$LOOPS" == 1) ]] ; then
  out=$(${executable} smt.string_solver=z3str3 unicode=false smt.str.tactic=3probe smt.arith.solver=2 ${INPUT})
else
  out=$(for i in `seq $SEQLOOPS` ; do ${executable} smt.string_solver=z3str3 unicode=false smt.str.tactic=3probe smt.arith.solver=2 ${INPUT} ; done > /dev/null ; ${executable} smt.string_solver=z3str3 unicode=false smt.str.tactic=3probe smt.arith.solver=2 ${INPUT})
fi

ret=$?
echo "result: ${out}"

exit ${ret}
