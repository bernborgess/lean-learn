#!/bin/bash

# Dynamic Variables
PROGRAM=SpeedFinesAreNotFine

TOTAL=3 # number of tests

# Language
LANG=lean

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
RESET='\033[0m'

# Check if source program exists
if [ ! -f "src/${PROGRAM}.${LANG}" ]; then
  echo -e "\n ${RED}x${RESET} Invalid Program name\n"
  exit 1
fi

# Runs tests against expected files
FAILED=0
for ((i=1; i<=TOTAL; i++)); do
  lean --run src/$PROGRAM.lean < "in/in${i}.txt" > "out/out${i}.txt"

  # cat "out/out${i}.txt"

  if diff  -b "out/out${i}.txt" "exp/exp${i}.txt" > /dev/null; then
    echo -e " ${GREEN}√${RESET} Test ${i} passed"
  else
    echo -e " ${RED}x${RESET} Test ${i} failed:"
    diff -b "out/out${i}.txt" "exp/exp${i}.txt"
    ((FAILED++))
  fi
done

# Displays final results
if [[ $FAILED -eq 0 ]]; then
  echo -e "\n ${GREEN}√${RESET} All Tests successful.\n"
else
  if [[ $FAILED -eq 1 ]]; then
    echo -e "\n ${RED}x${RESET} ${FAILED} Test failed.\n"
  else
    echo -e "\n ${RED}x${RESET} ${FAILED} Tests failed.\n"
  fi
fi
