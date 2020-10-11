#!/bin/bash

STGRED=../../src/tools/stgred.sh

STGPP=../../build/src/tools/stgpp

numtests=0
numfailures=0

# Folder tests
for i in fold-inputs/*.stg
do
  base="$(basename -- $i)"
  ((numtests++))

  ${STGPP} $i >/tmp/$base.out 2>/dev/null

  # drop comments, collapse file onto a single line, drop everything
  # before '(' and after ')'
  grep -v '//' /tmp/$base.out | tr '\n' ' ' | sed 's/^.*(/(/g' | sed 's/).*/)/g' >/tmp/$base

  if [[ $(< /tmp/$base) != "(i1 1)" ]]
  then
    echo -n "Expected folding to (i1 1) for : " 
    echo  $i
    cat /tmp/$base
    echo " "
    ((numfailures++))
  fi 
done

# STG duplication tests
for i in duplicated-inputs/*/
do
  base="$(basename -- $i)"
  ((numtests++))

  inputsOut="$(${STGRED} $i)" 
  if [ "$inputsOut" != $(< duplicated-inputs/$base.out) ];
  then
    echo -n "Expected " 
    echo -n duplicated-inputs/$base.out
    echo -n " for "
    echo -n $i
    echo -n ", but found "
    echo  "$inputsOut"
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
  exit 1
fi

