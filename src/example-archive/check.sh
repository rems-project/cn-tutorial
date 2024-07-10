#!/usr/bin/env bash

if [ -n "$1" ]
then
    echo "check.sh: using CN=$1 in $PWD"
    CN="$1"
else
    CN=cn
fi

process_files() {
  local dir=$1
  local pattern=$2
  local action=$3
  local action_argument=$4

  if [ -d "$dir" ]; then
    # Array to hold files matching the pattern
    local files=($(find "$dir" -maxdepth 1 -type f -name "$pattern" | sort))

    # Check if the array is not empty
    if [ "${#files[@]}" -gt 0 ]; then
      for file in "${files[@]}"; do
        # Ensure the file variable is not empty
        if [[ -n "$file" ]]; then
          "$action" "$file" "$action_argument"
        fi
      done
    else
      echo "No files matching '$pattern' found in $dir"
    fi
  else
    echo "Directory $dir does not exist"
  fi
}

failures=0

# ====================
# Check CN verification
# ====================

check_file() {
  local file=$1
  local expected_exit_code=$2

  printf "[$file]... "
  timeout 10 cn "$file" > /dev/null 2>&1
  local result=$?

  if [ $result -eq $expected_exit_code ]; then
    printf "\033[32mPASS\033[0m\n"
  else
    printf "\033[31mFAIL\033[0m (Unexpected return code: $result)\n"
    failures=$(( $failures + 1 ))
  fi
}

printf "== Check CN verification \n"
process_files "working" "*.c"               check_file 0
process_files "broken/error-cerberus" "*.c" check_file 2
process_files "broken/error-crash" "*.c"    check_file 125
process_files "broken/error-proof" "*.c"    check_file 1
process_files "broken/error-timeout" "*.c"  check_file 124
process_files "coq/broken-build" "*.c"      check_file 0
process_files "coq/broken-export" "*.c"     check_file 0
process_files "coq/working" "*.c"           check_file 0

# ====================
# Check Coq Exports
# ====================


# We allow several types of failure that can be intended
readonly SUCCESS=0
readonly FAIL_EXPORT=1
readonly FAIL_COQ_BUILD=2


check_coq_exports_end() {
    ## Call this funciton at the end of a coq export check. It will
    ## print the right message and return to the original directory
    ## with popd. It will also increse the failure count if necessary.
    local FAILED=$1
    local MESSAGE=$2
    
    if [[ $FAILED -ne 0 ]]; then
	printf "\033[31mFAIL\033[0m (${MESSAGE})\n"
	failures=$(( $failures + 1 ))
    else
	printf "\033[32mPASS\033[0m\n"
    fi
}
          
check_coq_exports() {
    local FILE=$1
    local FAIL_MODE=$2
    local PROTOTYPE_BUILD_DIR="../coq-build"
    local EXPORTED_LEMMAS="ExportedLemmas.v"
    local result=0 #^track if the build completed as much as expected
    
    printf "[$FILE]... "
    
    # Make a copy of the build directory but only if it doesn't
    # already exists
    local BUILD_DIR="${FILE%.*}-build"

    # Copy the build directory, and/or missing/new files
    rsync -a "${PROTOTYPE_BUILD_DIR}/" "$BUILD_DIR"
    
    # Export the CN lemmas
    cn "--lemmata=${BUILD_DIR}/theories/${EXPORTED_LEMMAS}" $FILE > /dev/null 2>&1
    # Check the result is as expected
    local cn_result=$?
    if [[ $cn_result -ne 0 && $FAIL_MODE -eq $FAIL_EXPORT ]]; then
	# The export is expected to fail and there is nothing else to
	# be done. Return successfully.
	check_coq_exports_end ${result} ""
	return ${result}
    elif [[ $cn_result -eq 0 && $FAIL_MODE -ne $FAIL_EXPORT ]]; then
	: # Export succeeded, as expected, continue the build
    else
	# Otherwise fail
        result=1
	check_coq_exports_end ${result} "Unexpected return code during export: $cn_result"
	return ${result}
    fi

    # The rest of the commands must be performed in the build directory 
    pushd "$BUILD_DIR" > /dev/null
    
    # Create the Coq Makefile
    # (We don't expect this to fail)
    coq_makefile -f _CoqProject -o Makefile.coq > /dev/null

    # Build the Coq files
    make -f Makefile.coq > /dev/null  2>&1
    # Check the result is as expected
    local coq_result=$?
    if [[ $coq_result -ne 0 && $FAIL_MODE -eq $FAIL_COQ_BUILD ]]; then
	# The coq build is expected to fail and there is nothing else to
	# be done. Return successfully.
	check_coq_exports_end ${result} ""
    elif [[ $coq_result -eq 0 && $FAIL_MODE -ne $FAIL_COQ_BUILD ]]; then
	# Export succeeded, as expected
        check_coq_exports_end ${result} ""
    else
        result=1
	check_coq_exports_end ${result} "Unexpected return code during coq build: $coq_result"
    fi

    # At this point everythink built successfully.

    # Return to the directory where the script was called (from the
    # build directory)
    popd > /dev/null

    return ${result}    
}

printf "== Check lemma export\n"
process_files "coq/working" "*.c"       check_coq_exports $SUCCESS
process_files "coq/broken-build" "*.c"  check_coq_exports $FAIL_COQ_BUILD
process_files "coq/broken-export" "*.c" check_coq_exports $FAIL_EXPORT


if [[ "$failures" = 0 ]]
then
  exit 0
else
  exit 1
fi
