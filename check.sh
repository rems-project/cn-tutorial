#!/bin/sh

good=0
bad=0

for file in build/solutions/*c; do
    if [[ $file == *.broken.c ]] ; then
        echo "(skipping $file)";
    else if cn $file ; then
        good=$(($good+1))
    else 
        bad=$(($bad+1))
    fi fi ;
done


echo "----------------------------"
echo "$good good, $bad bad"
echo "----------------------------"
