#!/usr/bin/env bash

TOTAL_FAILED=0
TOTAL_SUCCESS=0

run_and_capture() {
  r=$(stack run rules-$1-$2 2>/dev/null | grep -E "(FAIL|SUCCESS|WARNING|INFO|====>|>>>)" |
    (
      LOCAL_FAILED=0
      LOCAL_SUCCESS=0
      while IFS= read -r line; do
        echo "$line" 1>&2
        clean_line=$(sed -r 's/\x1B\[[0-9;]*[mK]//g' <<<"$line")
        if [[ $clean_line =~ ^\[SUCCESS\].* ]]; then
          export LOCAL_SUCCESS=$((LOCAL_SUCCESS + 1))
        elif [[ $clean_line =~ ^\[SUCCESS-Overall\].* ]]; then
          export LOCAL_SUCCESS=$((LOCAL_SUCCESS + 1))
        elif [[ $clean_line =~ ^\[SUCCESS-.*\].* ]]; then
          true
        elif [[ $clean_line =~ ^\[FAIL\].* ]]; then
          export LOCAL_FAILED=$((LOCAL_FAILED + 1))
        elif [[ $clean_line =~ ^\[FAIL-Overall\].* ]]; then
          export LOCAL_FAILED=$((LOCAL_FAILED + 1))
        elif [[ $clean_line =~ ^\[FAIL-.*\].* ]]; then
          true
        elif [[ $clean_line =~ ^\[WARNING\].* ]]; then
          true
        elif [[ $clean_line =~ ^\[INFO-.*\].* ]]; then
          true
        elif [[ $clean_line =~ ^\[INFO\].* ]]; then
          true
        elif [[ $clean_line =~ ^====\>.* ]]; then
          true
        elif [[ $clean_line =~ ^\>\>\>.* ]]; then
          true
        else
          echo "Unknown line: $clean_line"
          exit 1
        fi
      done
      echo "$LOCAL_SUCCESS $LOCAL_FAILED"
    ))
  r=($r)
  TOTAL_SUCCESS=$((TOTAL_SUCCESS + ${r[0]}))
  TOTAL_FAILED=$((TOTAL_FAILED + ${r[1]}))
}

framework=$1
if [[ -z $framework ]]; then
  echo "Usage: $0 <framework>"
  exit 1
fi

ALL_RULES=$(ls rules/$framework)
for rule in $ALL_RULES; do
  if [[ $rule != "generalize" ]]; then
    run_and_capture $framework $rule
  fi
done

echo "Total success: $TOTAL_SUCCESS"
echo "Total failed: $TOTAL_FAILED"
