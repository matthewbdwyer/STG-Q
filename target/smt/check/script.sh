#!/bin/bash

# sha_first="$(sha512sum stg_pc_0.stg| cut -d " " -f 1)"
# sha_second="$(sha512sum stg_pc_0\(copy\).stg| cut -d " " -f 1)"

if [ "$sha_first" == "$sha_second" ]
	then
		printf "Match"
		printf "\n $sha_second \n $sha_first"
	else
		printf "No match"
		printf "\n $sha_second \n $sha_first"
fi

printf "\n"