#!/bin/bash

STGRED=../../src/tools/stgred.sh

inputsOut="$(${STGRED} inputs)" 
if [ "$inputsOut" != "t1b.stg" ];
then
  echo "fail"
else
  echo "pass"
fi


