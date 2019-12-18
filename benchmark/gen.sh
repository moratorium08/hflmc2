#!/bin/sh

cd inputs

LISTS=`ls  | grep -E "[^n]$"`

mkdir -p ../lists
rm -f ../lists/all

for l in $LISTS
do
    find $l -depth 1 | grep -E ".*in" > ../lists/$l
    find $l -depth 1 | grep -E ".*in" >> ../lists/all
done

cd ../
# adhoc
mv lists/Burn_POPL18 lists/burn
mv lists/higher_nonterminating lists/nonterminating
