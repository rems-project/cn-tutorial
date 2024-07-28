#!/usr/bin/env bash
set -euo pipefail -o noclobber

CHECK_SCRIPT="$HOME/cerberus/tests/cn-runtime/cn-runtime-single-file.sh"

SCRIPT_OPT="-oq"

SUCCESS=$(find src/examples -name '*.c' \
    ! -name abs_mem_struct.c \
    ! -name "read.broken.c" \
    ! -name slf14_basic_succ_using_incr_attempt.broken.c)

# https://github.com/rems-project/cerberus/issues/444
BUGGY=("src/examples/abs_mem_struct.c")

SHOULD_FAIL=("src/examples/read.broken.c" "src/examples/slf14_basic_succ_using_incr_attempt.broken.c")

SUCCEEDED=""
FAILED=""

for FILE in ${SUCCESS}; do
  echo "Testing ${FILE} ..."
  "${CHECK_SCRIPT}" "${SCRIPT_OPT}" "${FILE}"
  if [ $? -eq 0 ]; then
    SUCCEEDED+=" ${FILE}"
  else
    FAILED+=" ${FILE}"
  fi
done

for FILE in ${SHOULD_FAIL}; do
  echo "Testing ${FILE} ..."
  "${CHECK_SCRIPT}" "${SCRIPT_OPT}" "${FILE}"
  if [ $? -ne 0 ]; then
    SUCCEEDED+=" ${FILE}"
  else
    FAILED+=" ${FILE}"
  fi
done

for FILE in ${BUGGY}; do
  echo "Testing ${FILE} ..."
  "${CHECK_SCRIPT}" "${SCRIPT_OPT}" "${FILE}"
  if [ $? -ne 0 ]; then
    SUCCEEDED+=" ${FILE}"
  else
    FAILED+=" ${FILE}"
  fi
done

echo "Succeeded: $SUCCEEDED"
echo "Failed: $FAILED"
