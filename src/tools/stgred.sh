#!/bin/bash

STGDIFF=${STGQ_BIN}/stgdiff.sh

shopt -s nullglob
files=($1/*.stg)
declare -A uniques

if [ ! -d "$2" ]; then
	mkdir "$2"
fi

for ((i=0; i<${#files[@]}; i++)); 
do
  duplicate="no"
  for ((j=i+1; j<${#files[@]}; j++)); 
  do
    ${STGDIFF} "${files[$i]}" "${files[$j]}" >/dev/null;
    if [ $? -eq 0 ];
    then
      # print out duplicates
      echo "$(basename -- "${files[$j]}")"
      duplicate="yes"
    fi
  done
  if [ "$duplicate" == "no" ]; then
	  name=$(basename -- "${files[$i]}")
	  if [ -d $2 ]; then
	  echo "$name is unique -- copying into $2"
	  cp ${files[$i]} $2
	  uniques[$name]=1
  	fi
  fi 
done

