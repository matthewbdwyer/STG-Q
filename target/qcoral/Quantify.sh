#!/bin/bash
# qcoral_path=${2:-/home/rishab/Music/qcoral}
qcoral_path=$QCORAL_HOME/qcoral
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

#Coverage
# gcov stgpp.cpp.gcno
# lcov --capture --directory . --output-file PN.info
# genhtml PN.info --output-directory OP5


declare -i no_out=0
declare -i total=$(ls $1 -1 | wc -l)

rm -rf /tmp/QCounter/qc/*
rm -rf /tmp/QCounter/stg/*
no_out+=1

folder_path=$(readlink -f $1)
num_samples=0


if [ $2 ]; then
	dictionary_path=$(readlink -f $2)
else
	dictionary_path="None"
fi

if [ $3 ]; then
	num_samples=$3
else
	num_samples=5000000
fi

files=$folder_path/*

#cd $STGQ_HOME/build/src/tools 																	#Changed this
declare -i nof=0
for file in $files
do
  if [[ "$file" == *".stg" ]]; then
	nof+=1
	stgpp "$folder_path/$(basename "$file")" > "/tmp/QCounter/stg/${nof}.stg"
  fi

done


cd $OLDPWD
#cd $STGQ_HOME/build/target/qcoral
files=/tmp/QCounter/stg/*

nof=0
for file in $files
do
	nof+=1
	if [[ "$dictionary_path" == "None" ]];then
		stg2qc "/tmp/QCounter/stg/$(basename "$file")" > "/tmp/QCounter/qc/${nof}.qcoral"
	else
		stg2qc "/tmp/QCounter/stg/$(basename "$file")" "$dictionary_path" > "/tmp/QCounter/qc/${nof}.qcoral"
	fi
done


files=/tmp/QCounter/qc/*
arr=""
for file in $files
do
	arr+="/tmp/QCounter/qc/$(basename $file)"
	arr+=' '
done

comb $arr
cd $OLDPWD
pw=$pwd
cd $qcoral_path
./run_qcoral.sh --mcIterativeImprovement --mcProportionalBoxSampleAllocation --mcSeed 123456 --mcMaxSamples $num_samples --mcInitialPartitionBudget 50000 --mcTargetVariance 1E-20 --mcSamplesPerIncrement 10000 "/tmp/QCounter/comb.qcoral" > "/tmp/QCounter/out/Result_${no_out}.out"

tail -1 "/tmp/QCounter/out/Result_${no_out}.out"
printf "\n"
cd $OLDPWD


# files=/tmp/QCounter/out/*

# for file in $files
# do
# 	tail -1 "/tmp/QCounter/out/$(basename $file)"
# 	printf "\n"
# done

printf "\n"
# ./res > "/tmp/QCounter/Final_result.out"

# tail -1 /tmp/QCounter/Final_result.out
