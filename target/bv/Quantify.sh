#!/bin/bash
# qcoral_path=${2:-/home/rishab/Music/qcoral}
qcoral_path=$STGQ_HOME/qcoral

printf "\nNOTE: Intermediate files will be stored in /tmp/QCounter\n";
if [ ! -d /tmp/QCounter ]
	then
		mkdir -p /tmp/QCounter/out
		mkdir /tmp/QCounter/smt
		mkdir /tmp/QCounter/stg
	else
		rm -rf /tmp/QCounter/*
		mkdir /tmp/QCounter/out
		mkdir /tmp/QCounter/smt
		mkdir /tmp/QCounter/stg
fi

# g++ -o comb QC_Combine.cpp
# g++ -o res QC_Result.cpp

declare -i no_out=0
declare -i total=$(ls $1 -1 | wc -l)

rm -rf /tmp/QCounter/smt/*
rm -rf /tmp/QCounter/stg/*
no_out+=1

folder_path=$(readlink -f $1)
dictionary_path=""
if [ $2 ]; then
	dictionary_path=$(readlink -f $2)
else
	dictionary_path="None"
fi
# printf "Folder name: $folder \n"
files=$folder_path/*

cd $STGQ_HOME/build/src/tools    																	#Changed this
declare -i nof=0
for file in $files
do
  if [[ "$file" == *".stg" ]]; then
	nof+=1
	./stgpp "$folder_path/$(basename "$file")" > "/tmp/QCounter/stg/${nof}.stg"
  fi

done

# Converting stg file to smt, then checking for uniqueness using sha512. If such smt file is already generated, delete the current smt file.

cd $OLDPWD
cd $STGQ_HOME/build/target/bv     															
files=/tmp/QCounter/stg/*

nof=0
for file in $files
do
	nof+=1
	if [[ "$dictionary_path" == "None" ]];then
		./stg2bv "/tmp/QCounter/stg/$(basename "$file")" > "/tmp/QCounter/smt/${nof}.smt"
	else
		./stg2bv "/tmp/QCounter/stg/$(basename "$file")" "$dictionary_path" > "/tmp/QCounter/smt/${nof}.smt"
	fi
	
	sha_this="$(sha512sum /tmp/QCounter/smt/${nof}.smt| cut -d " " -f 1)"
	all_files=/tmp/QCounter/smt/*

	for f in $all_files
	do
		if [ "${nof}.smt" == "$(basename "$f")" ]
		then
			continue
		fi

		sha_second="$(sha512sum "/tmp/QCounter/smt/$(basename "$f")"| cut -d " " -f 1)"

		if [ "$sha_this" == "$sha_second" ]
			then
				printf "${nof}.smt and $(basename "$f") have similar sha512sum. Removing ${nof}.smt.\n"
				rm "/tmp/QCounter/smt/${nof}.smt"
				break
		fi
	done 
done


# Now checking if any smt file implies any other smt file. Say, A.smt => B.smt, then A.smt is removed.

cd $OLDPWD
files=()
i=0

while read line
do
    files[ $i ]="$line"        
    (( i++ ))
done < <(ls "/tmp/QCounter/smt")

for (( i=0; i<${#files[@]}-1; i++ ))
do 
	for (( j=i+1; j<${#files[@]}; j++ ))
	do
		if [[ -f "/tmp/QCounter/smt/$(basename "${files[j]}")" ]]; then

			ans="$(python3 implication.py "/tmp/QCounter/smt/$(basename "${files[i]}")" "/tmp/QCounter/smt/$(basename "${files[j]}")")"
			IFS=$'\n' y=($ans)

			if [ "${y[0]}" == "proved" ]
			then
				printf "${files[i]} implies ${files[j]}\n"
				rm "/tmp/QCounter/smt/$(basename "${files[i]}")"
				break
			fi

			if [ "${y[-1]}" == "proved" ]
			then
				printf "${files[j]} implies ${files[i]}\n"
				rm "/tmp/QCounter/smt/$(basename "${files[j]}")"
			fi
		fi
	done
done


#-------------------------------
# files=/tmp/QCounter/qc/*
# arr=""
# for file in $files
# do
# 	arr+="/tmp/QCounter/qc/$(basename $file)"
# 	arr+=' '
# done

# cd $OLDPWD
# ./comb $arr
# pw=$pwd
# cd $qcoral_path
# ./run_qcoral.sh --mcIterativeImprovement --mcProportionalBoxSampleAllocation --mcSeed 123456 --mcMaxSamples 5000000 --mcInitialPartitionBudget 50000 --mcTargetVariance 1E-20 --mcSamplesPerIncrement 10000 "/tmp/QCounter/comb.qcoral" > "/tmp/QCounter/out/Result_${no_out}.out"

# tail -1 "/tmp/QCounter/out/Result_${no_out}.out"
# printf "\n"
# cd $OLDPWD
#-------------------------------

# files=/tmp/QCounter/out/*

# for file in $files
# do
# 	tail -1 "/tmp/QCounter/out/$(basename $file)"
# 	printf "\n"
# done

printf "\n"
# ./res > "/tmp/QCounter/Final_result.out"

# tail -1 /tmp/QCounter/Final_result.out
