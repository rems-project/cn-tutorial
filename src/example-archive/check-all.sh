#!/usr/bin/env bash 

SCRIPT_DIR="$(dirname "$(readlink -f "$0")")"

if [ -n "$1" ]
then
    echo "check-all.sh: using CN=$1 in $PWD"
    CN="$1"
else
    CN=cn
fi

subdirs=(
  "c-testsuite" 
  "dafny-tutorial" 
  "java_program_verification_challenges" 
  "should-fail"
  "open-sut"
  "Rust" 
  "SAW" 
  "simple-examples"
)
FAILURE=0 

for subdir in "${subdirs[@]}"; do
  cd "$SCRIPT_DIR/$subdir" || continue

  ../check.sh "$CN"

  if [ $? != 0 ]
  then 
    FAILURE=1
  fi 
done

if [ $FAILURE -eq 0 ];
then
    printf "\n\033[32mTest suite passes:\033[0m all CN tests in the example archive produced expected return codes\n"
    exit 0
else 
    printf "\n\033[31mTest suite fails:\033[0m one or more CN tests in the example archive produced an unexpected return code\n"
    exit 1
fi