#!/usr/bin/env bash

if [ -n "$1" ]
then
    echo "using CN=$1 in $PWD"
    CN="$1"
else
    CN=cn
fi

good=0
bad=0

for file in src/examples/*c;
do
    echo "Checking $file ..."
    $CN $file 
    retval=$?
    if [[ $file == *.broken.c ]]
    then
        if [[ $retval -eq 1 ]]; 
        then
            good=$(($good+1))
        else
            bad=$(($bad+1))
        fi
    else
        if [[ $retval -eq 0 ]]; 
        then
            good=$(($good+1))
        else
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
  exit 1
fi

