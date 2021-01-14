#!/bin/bash

STGDIFF=${STGQ_BIN}/stgdiff.sh

shopt -s nullglob
files=($1/*.stg)

for ((i=0; i<${#files[@]}; i++)); 
do
  for ((j=i+1; j<${#files[@]}; j++)); 
  do
    ${STGDIFF} "${files[$i]}" "${files[$j]}" >/dev/null;
    if [ $? -eq 0 ];
    then
      echo "$(basename -- "${files[$j]}")"
    fi
  done
done

