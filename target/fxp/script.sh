#!/bin/bash

# sha_first="$(sha512sum stg_pc_0.stg| cut -d " " -f 1)"
# sha_second="$(sha512sum stg_pc_0\(copy\).stg| cut -d " " -f 1)"

# ans="$(python implication.py /tmp/QCounter/smt/1.smt /tmp/QCounter/smt/4.smt)"
# IFS=$'\n' y=($ans)

# if [ "${y[0]}" == "proved" ]
# then
# 	printf "First implies second\n"
# fi

# if [ "${y[-1]}" == "proved" ]
# then
# 	printf "Second implies first\n"
# fi
# printf "\n${y[-1]}\n"

files=()
i=0
while read line
do
    files[ $i ]="$line"        
    (( i++ ))
done < <(ls "/tmp/QCounter/smt")


# echo "${#files[@]}"

for (( i=0; i<${#files[@]}-1; i++ ))
do 
	for (( j=i+1; j<${#files[@]}; j++ ))
	do
		ans="$(python implication.py "/tmp/QCounter/smt/$(basename "${files[i]}")" "/tmp/QCounter/smt/$(basename "${files[j]}")")"

		IFS=$'\n' y=($ans)

		printf "$y"

		if [ "${y[0]}" == "proved" ]
		then
			printf "First implies second\n"
			rm "/tmp/QCounter/smt/$(basename "${files[i]}")"
			break
		fi

		if [ "${y[-1]}" == "proved" ]
		then
			printf "First implies second\n"
			rm "/tmp/QCounter/smt/$(basename "${files[j]}")"
		fi
	done
done