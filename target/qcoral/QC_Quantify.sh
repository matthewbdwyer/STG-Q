#!/bin/bash

file_path=$1
qcoral_path=${2:-/home/rishab/Downloads/qcoral-fse-replication/qcoral}
files=$file_path/*
printf "\nNOTE: Intermediate files will be stored in /tmp/QCounter\n";

if [ ! -d /tmp/QCounter ]
then
	mkdir -p /tmp/QCounter
else
	rm -rf /tmp/QCounter/*
fi

cd ../../build/target/qcoral
declare -i nof=0
for file in $files
do
  nof+=1
  ./stg2qc "$file_path/$(basename "$file")" > "/tmp/QCounter/${nof}.qcoral"
done

files=/tmp/QCounter/*
for file in $files
do
	arr+="/tmp/QCounter/$(basename $file)"
	arr+=' '
done

cd -
g++ -o comb QC_Combine.cpp
./comb $arr
pwd=$pwd
cd $qcoral_path
./run_qcoral.sh --mcIterativeImprovement --mcProportionalBoxSampleAllocation --mcSeed 123456 --mcMaxSamples 5000000 --mcInitialPartitionBudget 50000 --mcTargetVariance 1E-20 --mcSamplesPerIncrement 10000 "/tmp/QCounter/comb.qcoral" > "/tmp/QCounter/Result.out"

printf "\nQuantification Result:\n"
tail -1 /tmp/QCounter/Result.out
printf "\n"

