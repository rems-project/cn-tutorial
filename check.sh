#!/usr/bin/env bash

SCRIPT_DIR="$(dirname "$(readlink -f "$0")")"

if [ -n "$1" ]
then
    echo "using CN=$1 in $PWD"
    CN="$1"
else
    CN=cn
fi

good=0
bad=0
declare -a bad_tests

for file in $SCRIPT_DIR/src/examples/*c;
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

