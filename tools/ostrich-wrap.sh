#!/usr/bin/env bash

INPUT=$1
LOOPS=$2
let SEQLOOPS=$LOOPS-1
echo "$SEQLOOPS"

SCRIPT_DIR="/tools"
OSTRICH_PROG="${SCRIPT_DIR}/ostrich"

if [[ ("$LOOPS" == 1) ]] ; then
  out=$(${OSTRICH_PROG} +quiet -portfolio=strings ${INPUT})
else
  out=$(for i in `seq $SEQLOOPS` ; do ${OSTRICH_PROG} +quiet -portfolio=strings ${INPUT}; done > /dev/null ; ${OSTRICH_PROG} +quiet -portfolio=strings ${INPUT})
fi

ret=$?
echo "result: ${out}"

exit ${ret}
