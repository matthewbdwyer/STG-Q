#!/bin/bash

STGRED=$STGQ_BIN/stgred.sh
STGPP=$STGQ_BIN/stgpp

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
    echo -n "TEST folding[$base]: FAIL: Expected folding to (i1 1) for : " 
    echo  $i
    cat /tmp/$base
    echo " "
    ((numfailures++))
  else
    echo "TEST folding[$base]: PASS"
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
    echo -n "TEST dedup[$base]: FAIL"
    echo -n "Expected " 
    echo -n duplicated-inputs/$base.out
    echo -n " for "
    echo -n $i
    echo -n ", but found "
    echo  "$inputsOut"
    ((numfailures++))
  else
    echo "TEST dedup[$base]: PASS"
  fi
done

if [ ! ${numfailures} -eq "0" ]; then
  echo -n "fail : "
  echo -n ${numfailures}/${numtests}
  echo " tests failed"
  exit 1
fi

