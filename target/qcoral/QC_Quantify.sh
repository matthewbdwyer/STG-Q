#!/bin/bash
qcoral_path=${2:-/home/rishab/Downloads/qcoral-fse-replication/qcoral}
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

g++ -o comb QC_Combine.cpp
g++ -o res QC_Result.cpp

declare -i no_out=0
declare -i total=$(ls $1 -1 | wc -l)
total=$[total - 1]
# declare -i total=$(ls $1 -1 | grep "^d" | wc -l)

printf "Total folders to test: $total \n"

printf "Testing folders: 0/${total} \n"

for folder in $1/*
do
	if [ ! -d $folder ]; then
		continue
	fi

	if [ ! -f $folder/expected.txt ]; then
		printf "TEST %-30s: SKIP\n" $folder
		total=$[total - 1]
		continue
	fi

	rm -rf /tmp/QCounter/qc/*
	rm -rf /tmp/QCounter/stg/*
	no_out+=1
	exp=""

	folder_path=$folder
	dictionary_path="$folder_path/dict.json"
	# printf "Folder name: $folder \n"
	files=$folder_path/*

	cd ../../build/src/tools																		#Changed this
	declare -i nof=0
	for file in $files
	do
	  if [[ "$file" == *".stg" ]]; then
		nof+=1
		./stgpp "$folder_path/$(basename "$file")" "$dictionary_path" > "/tmp/QCounter/stg/${nof}.stg"
	  fi

	  if [[ "$file" =~ "expected" ]]; then
	  	while IFS= read -r line
	  	do
	  		exp="$line"
	  	done < "$file"

	  	# printf "Hrere \n"
		# cp "$folder_path/$(basename "$file")" "/tmp/QCounter/out/Expected_${no_out}.txt"
	  fi
	done

	if [[ "$exp" == "" ]]; then
		printf "No expected output file in: $folder \n"
		exit 125
	fi


	cd $OLDPWD
	cd ../../build/target/qcoral           															#Changed this
	files=/tmp/QCounter/stg/*

	nof=0
	for file in $files
	do
		nof+=1
		./stg2qc "/tmp/QCounter/stg/$(basename "$file")" "$dictionary_path" > "/tmp/QCounter/qc/${nof}.qcoral"
	done


	files=/tmp/QCounter/qc/*
	arr=""
	for file in $files
	do
		arr+="/tmp/QCounter/qc/$(basename $file)"
		arr+=' '
	done

	cd $OLDPWD
	./comb $arr
	pw=$pwd
	cd $qcoral_path
	echo -e "\e[1A\e[KTesting folders: ${no_out}/${total}"
	./run_qcoral.sh --mcIterativeImprovement --mcProportionalBoxSampleAllocation --mcSeed 123456 --mcMaxSamples 5000000 --mcInitialPartitionBudget 50000 --mcTargetVariance 1E-20 --mcSamplesPerIncrement 10000 "/tmp/QCounter/comb.qcoral" > "/tmp/QCounter/out/Result_${no_out}.out"
	
	printf "$exp\n" >> "/tmp/QCounter/out/Result_${no_out}.out"

	cd $OLDPWD

done

printf "\n"

./res

printf "\n"
# ./res > "/tmp/QCounter/Final_result.out"

# tail -1 /tmp/QCounter/Final_result.out