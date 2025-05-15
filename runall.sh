#!/usr/bin/env bash

TOTAL_FAILED=0
TOTAL_SUCCESS=0

run_and_capture() {
  r=$(stack run $1 2>/dev/null | grep -E "(FAIL|SUCCESS|WARNING|INFO|====>|>>>)" |
    (
      LOCAL_FAILED=0
      LOCAL_SUCCESS=0
      while IFS= read -r line; do
        echo $line 1>&2
        if [[ $line =~ ^\[SUCCESS\].* ]]; then
          export LOCAL_SUCCESS=$((LOCAL_SUCCESS + 1))
        elif [[ $line =~ ^\[SUCCESS-Overall\].* ]]; then
          export LOCAL_SUCCESS=$((LOCAL_SUCCESS + 1))
        elif [[ $line =~ ^\[SUCCESS-.*\].* ]]; then
          true
        elif [[ $line =~ ^\[FAIL\].* ]]; then
          export LOCAL_FAILED=$((LOCAL_FAILED + 1))
        elif [[ $line =~ ^\[FAIL-Overall\].* ]]; then
          export LOCAL_FAILED=$((LOCAL_FAILED + 1))
        elif [[ $line =~ ^\[FAIL-.*\].* ]]; then
          true
        elif [[ $line =~ ^\[WARNING\].* ]]; then
          true
        elif [[ $line =~ ^\[INFO-.*\].* ]]; then
          true
        elif [[ $line =~ ^\[INFO\].* ]]; then
          true
        elif [[ $line =~ ^====\>.* ]]; then
          true
        elif [[ $line =~ ^\>\>\>.* ]]; then
          true
        else
          echo "Unknown line: $line"
          exit 1
        fi
      done
      echo "$LOCAL_SUCCESS $LOCAL_FAILED"
    ))
  r=($r)
  TOTAL_SUCCESS=$((TOTAL_SUCCESS + ${r[0]}))
  TOTAL_FAILED=$((TOTAL_FAILED + ${r[1]}))
}

ALL_RULES=$(ls rules/cs526)
for rule in $ALL_RULES; do
  rule=${rule%.hs}
  if [[ $rule != "pad-concat" ]]; then
    run_and_capture $rule
  fi
done

echo "Total success: $TOTAL_SUCCESS"
echo "Total failed: $TOTAL_FAILED"
