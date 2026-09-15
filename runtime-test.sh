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
            ! -name "00010_non_termination.c" \
            ! -name "cast1.c" \
            ! -name "cast2.c" \
            ! -name "cast3.c" \
            ! -name "cast4.c" \
            ! -name "for_1.c" \
            ! -name "for_3.c" \
            ! -name "list_2.c" \
            ! -name "list_3.c" \
            ! -name "loop_2.c" \
            ! -name "loop_8.c" \
            ! -name "pointer_dec2.c" \
            ! -name "string_1.c" \
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
       src/example-archive/java_program_verification_challenges/working/00010_non_termination.c \
       src/example-archive/simple-examples/working/for_1.c \
       src/example-archive/simple-examples/working/for_3.c \
       src/example-archive/simple-examples/working/loop_8.c \
       src/example-archive/simple-examples/working/pointer_dec2.c \
       src/example-archive/simple-examples/working/string_1.c \
    "

SHOULD_FAIL=$(find src/example-archive/*/broken -name '*.c')
SHOULD_FAIL+=("src/example-archive/c-testsuite/working/00094.working.c ")
# These examples use VIP, which is unsupported in Fulminate (Sep 2026)
SHOULD_FAIL+=("\
                src/example-archive/simple-examples/working/cast_1.c \
                src/example-archive/simple-examples/working/cast_2.c \
                src/example-archive/simple-examples/working/cast_3.c \
                src/example-archive/simple-examples/working/cast_4.c")
# For these list examples, I suspect the runtime lemma failure is legitimate 
# and there is either something wrong with the specification, or the driver
# constructs a list of the wrong shape.
SHOULD_FAIL+=("\ 
                src/example-archive/simple-examples/working/list_2.c \
                src/example-archive/simple-examples/working/list_3.c \
             ")

# Infinite loop times out
SHOULD_FAIL+=("\ 
                src/example-archive/simple-examples/working/loop_2.c \
             ")

# Uninterpreted functions unsupported for testing
SHOULD_FAIL+=("\ 
                src/example-archive/simple-examples/working/power_1.c \
                src/example-archive/simple-examples/working/power_2.c \
             ")

FAILED=""

for FILE in ${SUCCESS}; do
  if ! exits_with_code "${FILE}" 0; then
    FAILED+=" ${FILE}"
  fi
done

# for FILE in ${SHOULD_FAIL}; do
#   if exits_with_code "${FILE}" 0; then
#     FAILED+=" ${FILE}"
#   fi
# done

# for FILE in ${BUGGY}; do
#   if exits_with_code "${FILE}" 0; then
#     FAILED+=" ${FILE}"
#   fi
# done

if [ -z "${FAILED}" ]; then
  exit 0
else
  printf "\033[31mFAILED: ${FAILED}\033[0m\n"
  exit 1
fi