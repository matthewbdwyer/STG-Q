#!/bin/bash
# qcoral_path=${2:-/home/rishab/Music/qcoral}
qcoral_path=$QCORAL_HOME/qcoral
# pysmt_path=/home/rishab/Downloads/pysmt/pysmt
pysmt_path=$PYSMT

printf "\nNOTE: Intermediate files will be stored in /tmp/QCounter\n";
if [ ! -d /tmp/QCounter ]
	then
		mkdir -p /tmp/QCounter/out
		mkdir /tmp/QCounter/smt
		mkdir /tmp/QCounter/fxp
		mkdir /tmp/QCounter/stg
	else
		rm -rf /tmp/QCounter/*
		mkdir /tmp/QCounter/out
		mkdir /tmp/QCounter/smt
		mkdir /tmp/QCounter/stg
		mkdir /tmp/QCounter/fxp
fi

# g++ -o comb QC_Combine.cpp
# g++ -o res QC_Result.cpp

declare -i no_out=0
declare -i total=$(ls $1 -1 | wc -l)

rm -rf /tmp/QCounter/smt/*
rm -rf /tmp/QCounter/stg/*
rm -rf /tmp/QCounter/fxp/*

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

# cd $STGQ_HOME/build/src/tools    																	#Changed this
declare -i nof=0
for file in $files
do
  if [[ "$file" == *".stg" ]]; then
	nof+=1
	stgpp "$folder_path/$(basename "$file")" > "/tmp/QCounter/stg/${nof}.stg"
  fi

done

cd $OLDPWD
# cd $STGQ_HOME/build/target/bv     															
files=/tmp/QCounter/stg/*

nof=0
for file in $files
do
	nof+=1
	if [[ "$dictionary_path" == "None" ]];then
		stg2fxp "/tmp/QCounter/stg/$(basename "$file")" > "/tmp/QCounter/fxp/${nof}.fxp"
	else
		stg2fxp "/tmp/QCounter/stg/$(basename "$file")" "$dictionary_path" > "/tmp/QCounter/fxp/${nof}.fxp"
	fi
	 
done

# echo "HELLOOOOOOOOOO"

cd $OLDPWD

python3 combine.py > /tmp/QCounter/fxp/comb.fxp

files=()
i=0

while read line
do
    files[ $i ]="$line"        
    (( i++ ))
done < <(ls "/tmp/QCounter/fxp")

for (( i=0; i<${#files[@]}; i++ ))
do 
	python3 "$pysmt_path/pysmt/conv_fxp_smt.py" "/tmp/QCounter/fxp/$(basename "${files[i]}")" > "/tmp/QCounter/smt/$(basename "${files[i]}")"
done

for f in /tmp/QCounter/smt/*; do 
    mv -- "$f" "${f%.fxp}.smt"
done


# cp -r /tmp/QCounter/smt "/home/rishab/Documents/fxp/$(basename $folder_path)"

rm -rf "$folder_path/bv"
cp -r /tmp/QCounter/smt "$folder_path/bv"

printf "\n"

