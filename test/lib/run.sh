#!/bin/bash

STGPP=../../build/src/tools/stgpp

numtests=0
numfailures=0

# Parser passing tests
for i in parsetype-inputs/pass/*.stg
do
  base="$(basename -- $i)"
  ((numtests++))

  # drop comments, collapse file onto a single line, then add newlines to separate
  # dictionary and constraint on separate lines, to isolate every sub-expression on 
  # its own line, and to ensure the file ends with a newline
  grep -v '//' $i | tr '\n' ' ' | sed 's/]/]\n/g' | sed 's/(/(\n/g' | sed 's/)/\n)/g' | sed -e '$a\' >/tmp/$base

  ${STGPP} -no-constant-folding $i >$i.out
  grep -v '//' $i.out | tr '\n' ' ' | sed 's/]/]\n/g' | sed 's/(/(\n/g' | sed 's/)/\n)/g' >/tmp/$base.out

  # ignore whitespace in diffing the files
  diff -b -w /tmp/$base /tmp/$base.out >/tmp/$base.diff

  if [[ -s /tmp/$base.diff ]]
  then
    echo -n "Test differences for : " 
    echo $i
    cat /tmp/$base.diff
    ((numfailures++))
  fi 
done

# Parser and type checker failing tests
for i in parsetype-inputs/fail/*.stg
do
  base="$(basename -- $i)"
  ((numtests++))

  ${STGPP} -no-constant-folding $i >$i.out 2>/dev/null

  # This catches "Parse error" or "Type error"
  if ! cat $i.out | grep -q "error";
  then
    echo -n "Expected failure for : " 
    echo $i
    ((numfailures++))
  fi 
done

if [ ${numfailures} -eq "0" ]; 
then
  echo "pass"
else
  echo -n "fail : "
  echo -n ${numfailures}/${numtests}
  echo " tests failed"
fi
  
