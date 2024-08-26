#!/usr/bin/env bash

SCRIPT_DIR="$(dirname "$(readlink -f "$0")")"

if [ -n "$1" ]
then
    echo "using CN=$1 in $PWD"
    CN="$1"
else
    CN="cn verify"
fi

good=0
bad=0
declare -a bad_tests

# https://github.com/rems-project/cerberus/pull/494 exposed an issue in
# the Z3 which is a bit difficult to work around in the implementation
# itself and so we have this hacky work-around instead whilst it is fixed
# upstream https://github.com/Z3Prover/z3/issues/7352
if [[ "${CN}" == "cn verify" ]] \
    || [[ "${CN}" == *"--solver-type=z3"* ]]; then
    FILES=($(find "${SCRIPT_DIR}/src/examples" -name '*.c' \
        ! -name queue_pop.c \
        ! -name queue_push_induction.c))
else
    FILES=($(find "${SCRIPT_DIR}/src/examples" -name '*.c'))
fi

for file in "${FILES[@]}"
do
    echo "Checking $file ..."
    $CN $file 
    retval=$?
    if [[ $file == *.broken.c ]]
    then
        if [[ $retval -ne 0 ]]; 
        then
            good=$(($good+1))
        else
            bad_tests[$bad]=$file
            bad=$(($bad+1))
        fi
    else
        if [[ $retval -eq 0 ]]; 
        then
            good=$(($good+1))
        else
            bad_tests[$bad]=$file
            bad=$(($bad+1))
        fi
    fi
done

echo "----------------------------"
echo "$good good, $bad bad"
echo "----------------------------"


if [[ "$bad" = 0 ]]
then
  exit 0
else
  echo "Failed tests:"
  for file in ${bad_tests[@]}; do
    echo $file
  done
  exit 1
fi

