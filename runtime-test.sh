#!/usr/bin/env bash
set -euo pipefail -o noclobber

function echo_and_err() {
    printf "$1\n"
    exit 1
}

[ $# -eq 0 ] || echo_and_err "USAGE: $0"

RUNTIME_PREFIX="$OPAM_SWITCH_PREFIX/lib/cn/runtime"
[ -d "${RUNTIME_PREFIX}" ] || echo_and_err "Could not find CN's runtime directory (looked at: '${RUNTIME_PREFIX}')"

function exits_with_code() {
  local file=$1
  local expected_exit_code=$2

  printf "[$file]... "
  timeout 20 cn instrument --run "$file" --no-debug-info --tmp --print-steps -DCN_INSTRUMENT &> /dev/null
  local result=$?

  if [ $result -eq $expected_exit_code ]; then
    printf "\033[32mPASS\033[0m\n"
    return 0
  else
    printf "\033[31mFAIL\033[0m (Unexpected return code: $result)\n"
    return 1
  fi
}

SUCCESS=$(find src/example-archive/*/working -name '*.c' \
            ! -name "00052.working.c" \
            ! -name "00120.working.c" \
            ! -name "00053.working.c" \
            ! -name "00112.working.c" \
            ! -name "00007.working.c" \
            ! -name "00090.working.c" \
            ! -name "00032.c" \
            ! -name "00044.working.c" \
            ! -name "00006.working.c" \
            ! -name "00094.working.c" \
        )

BUGGY="\
       src/example-archive/c-testsuite/working/00052.working.c \
       src/example-archive/c-testsuite/working/00120.working.c \
       src/example-archive/c-testsuite/working/00053.working.c \
       src/example-archive/c-testsuite/working/00112.working.c \
       src/example-archive/c-testsuite/working/00007.working.c \
       src/example-archive/c-testsuite/working/00090.working.c \
       src/example-archive/c-testsuite/working/00032.c \
       src/example-archive/c-testsuite/working/00044.working.c \
       src/example-archive/c-testsuite/working/00006.working.c \
    "

SHOULD_FAIL=$(find src/example-archive/*/broken -name '*.c')
SHOULD_FAIL+=("\
                src/example-archive/c-testsuite/working/00094.working.c \
             ")

FAILED=""

for FILE in ${SUCCESS}; do
  if ! exits_with_code "${FILE}" 0; then
    FAILED+=" ${FILE}"
  fi
done

for FILE in ${SHOULD_FAIL}; do
  if ! exits_with_code "${FILE}" 1; then
    FAILED+=" ${FILE}"
  fi
done

for FILE in ${BUGGY}; do
  if ! exits_with_code "${FILE}" 1; then
    FAILED+=" ${FILE}"
  fi
done

if [ -z "${FAILED}" ]; then
  exit 0
else
  printf "\033[31mFAILED: ${FAILED}\033[0m\n"
  exit 1
fi