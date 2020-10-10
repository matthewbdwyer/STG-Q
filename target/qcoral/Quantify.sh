#!/bin/bash

if [ -z "$QCORAL_HOME" ]; then
	echo "Environment variable QCORAL_HOME is undefined"
	exit 1
fi

printf "\nNOTE: Intermediate files will be stored in /tmp/QCounter\n";
if [ ! -d /tmp/QCounter ]
	then
		mkdir -p /tmp/QCounter/out
		mkdir /tmp/QCounter/qc
		mkdir /tmp/QCounter/stg
	else
		rm -rf /tmp/QCounter/*
		mkdir /tmp/QCounter/out
		mkdir /tmp/QCounter/qc
		mkdir /tmp/QCounter/stg
fi

declare -i no_out=0
declare -i total=$(ls $1 -1 | wc -l)

rm -rf /tmp/QCounter/qc/*
rm -rf /tmp/QCounter/stg/*
no_out+=1

folder_path=$(realpath $1)
files=$folder_path/*

declare -i nof=0
for file in $files
do
  if [[ "$file" == *".stg" ]]; then
	nof+=1
	stgpp "$folder_path/$(basename "$file")" > "/tmp/QCounter/stg/${nof}.stg"
  fi
done

files=/tmp/QCounter/stg/*

nof=0
for file in $files
do
	nof+=1
	stg2qc "/tmp/QCounter/stg/$(basename "$file")" > "/tmp/QCounter/qc/${nof}.qcoral"
done


files=/tmp/QCounter/qc/*
arr=""
for file in $files
do
	arr+="/tmp/QCounter/qc/$(basename $file)"
	arr+=' '
done

comb $arr
pushd $QCORAL_HOME >/dev/null
#
# to run qcoral you need to be in the proper directory
#
./run_qcoral.sh --mcIterativeImprovement --mcProportionalBoxSampleAllocation --mcSeed 123456 --mcMaxSamples 5000000 --mcInitialPartitionBudget 50000 --mcTargetVariance 1E-20 --mcSamplesPerIncrement 10000 "/tmp/QCounter/comb.qcoral" > "/tmp/QCounter/out/Result_${no_out}.out"

tail -1 "/tmp/QCounter/out/Result_${no_out}.out"
printf "\n"
popd >/dev/null

# files=/tmp/QCounter/out/*

# for file in $files
# do
# 	tail -1 "/tmp/QCounter/out/$(basename $file)"
# 	printf "\n"
# done

#printf "\n"
# ./res > "/tmp/QCounter/Final_result.out"

# tail -1 /tmp/QCounter/Final_result.out
