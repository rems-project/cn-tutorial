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

function exits_with_error_code() {
  local file=$1

  printf "[$file]... "
  timeout 20 cn instrument --run "$file" --no-debug-info --tmp --print-steps -DCN_INSTRUMENT &> /dev/null
  local result=$?

  if [ $result -gt 0 ]; then
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
            ! -name "cast_1.c" \
            ! -name "cast_2.c" \
            ! -name "cast_3.c" \
            ! -name "cast_4.c" \
            ! -name "for_1.c" \
            ! -name "for_3.c" \
            ! -name "list_2.c" \
            ! -name "list_3.c" \
            ! -name "loop_2.c" \
            ! -name "loop_6.c" \
            ! -name "loop_8.c" \
            ! -name "pointer_dec2.c" \
            ! -name "string_1.c" \
            ! -name "power_1.c" \
            ! -name "power_2.c" \
        )

# Add files that fail for proof but are legitimate for testing and pass
SUCCESS+=("\ 
            src/example-archive/c-testsuite/broken/error-proof/00008.err1.c \
            src/example-archive/c-testsuite/broken/error-proof/00073.err1.c \
            src/example-archive/c-testsuite/broken/error-proof/00010.err1.c \
            src/example-archive/c-testsuite/broken/error-proof/00034.err1.c \
            src/example-archive/c-testsuite/broken/error-proof/00092.err1.c \
            src/example-archive/c-testsuite/broken/error-proof/00147.err1.c \
            src/example-archive/c-testsuite/broken/error-proof/00143.err1.c \
            src/example-archive/c-testsuite/broken/error-proof/00130.err1.c \
            src/example-archive/c-testsuite/broken/error-proof/00141.err1.c \
            src/example-archive/c-testsuite/broken/error-proof/00041.err1.c \
            src/example-archive/c-testsuite/broken/error-proof/00088.err1.c \
            src/example-archive/c-testsuite/broken/error-proof/00148.err1.c \
            src/example-archive/c-testsuite/broken/error-proof/00103.err1.c \
            src/example-archive/c-testsuite/broken/error-proof/00101.err1.c \
            src/example-archive/c-testsuite/broken/error-proof/00117.err1.c \
            src/example-archive/c-testsuite/broken/error-proof/00133.err1.c \
            src/example-archive/c-testsuite/broken/error-proof/00077.err1.c \
            src/example-archive/c-testsuite/broken/error-proof/00142.err1.c \
            src/example-archive/c-testsuite/broken/error-proof/00040.err1.c \
            src/example-archive/should-fail/broken/error-proof/overflow_neg_1.c \
            src/example-archive/should-fail/broken/error-proof/overflow_neg_2.c \
            src/example-archive/simple-examples/broken/error-proof/loop_4.c \
            src/example-archive/simple-examples/broken/error-proof/case_timeout.c \
            src/example-archive/simple-examples/broken/error-proof/ownership_1.c \
")

# Excluding files that:
# - are ported from other test suites (time/bandwidth reasons)
# - proof is not supposed to handle but testing passes for
# - are buggy in Fulminate but should legitimately fail
SHOULD_FAIL=$(find src/example-archive/*/broken -name '*.c' \
            ! -path '*/Rust/*' \
            ! -path '*/SAW/*' \
            ! -path '*/dafny-tutorial/*' \
            ! -path '*/java_program_verification_challenges/*' \
            ! -path '*/coq-lemmas/*' \
            ! -path '*/open-sut/*' \
            ! -name "00008.err1.c" \
            ! -name "00073.err1.c" \
            ! -name "00010.err1.c" \
            ! -name "00034.err1.c" \
            ! -name "00092.err1.c" \
            ! -name "00147.err1.c" \
            ! -name "00143.err1.c" \
            ! -name "00130.err1.c" \
            ! -name "00141.err1.c" \
            ! -name "00041.err1.c" \
            ! -name "00088.err1.c" \
            ! -name "00148.err1.c" \
            ! -name "00103.err1.c" \
            ! -name "00101.err1.c" \
            ! -name "00117.err1.c" \
            ! -name "00133.err1.c" \
            ! -name "00077.err1.c" \
            ! -name "00142.err1.c" \
            ! -name "00040.err1.c" \
            ! -name "overflow_neg_1.c" \
            ! -name "overflow_neg_2.c" \
            ! -name "loop_4.c" \
            ! -name "case_timeout.c" \
            ! -name "ownership_1.c" \
            ! -name "00011_dependen_specifications.c" \
            \
            ! -name "00138.err1.c" \
            ! -name "00026.err1.c" \
            ! -name "00124.err1.c" \
            ! -name "00151.err1.c" \
            ! -name "00137.err1.c" \
            ! -name "00058.err1.c" \
            ! -name "00115.err1.c" \
            ! -name "pointer_dec3.c" \
            ! -name "self_ref_init.c" \
        )

# SHOULD_FAIL=""
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

# Loop timeout. loop_2 is infinite, loop_6 just a large # of iterations
SHOULD_FAIL+=("\ 
                src/example-archive/simple-examples/working/loop_2.c \
                src/example-archive/simple-examples/working/loop_6.c \
             ")

# Uninterpreted functions unsupported for testing
SHOULD_FAIL+=("\ 
                src/example-archive/simple-examples/working/power_1.c \
                src/example-archive/simple-examples/working/power_2.c \
             ")

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
       src/example-archive/c-testsuite/broken/error-proof/00138.err1.c \
       src/example-archive/c-testsuite/broken/error-proof/00026.err1.c \
       src/example-archive/c-testsuite/broken/error-proof/00124.err1.c \
       src/example-archive/c-testsuite/broken/error-proof/00151.err1.c \
       src/example-archive/c-testsuite/broken/error-proof/00137.err1.c \
       src/example-archive/c-testsuite/broken/error-proof/00058.err1.c \
       src/example-archive/simple-examples/broken/error-proof/pointer_dec3.c \
       src/example-archive/simple-examples/broken/error-proof/self_ref_init.c \
    "


FAILED=""

for FILE in ${SUCCESS}; do
  if ! exits_with_code "${FILE}" 0; then
    FAILED+=" ${FILE}"
  fi
done

for FILE in ${SHOULD_FAIL}; do
  if ! exits_with_error_code "${FILE}"; then
    FAILED+=" ${FILE}"
  fi
done

for FILE in ${BUGGY}; do
  if ! exits_with_error_code "${FILE}"; then
    FAILED+=" ${FILE}"
  fi
done

if [ -z "${FAILED}" ]; then
  exit 0
else
  printf "\033[31mFAILED: ${FAILED}\033[0m\n"
  exit 1
fi