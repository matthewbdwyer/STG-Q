#!/bin/bash

cd $(dirname $(readlink -f "$0"))

exit_code=0
for test_directory in `ls`
do
	# skip non-directories
	if [ ! -d $test_directory ]; then
		continue
	fi

	# no expected.txt file, so skip
	if [ ! -f $test_directory/expected.txt ]; then
		continue
	fi

	# output of quantify: [qCORAL:results] samples=5000000, mean=2.499708e-01, variance=3.749708e-08, time=4.682822, stdev=1.936416e-04

	mean=$(Quantify.sh $test_directory 2>/dev/null | grep mean | cut -d',' -f2 | cut -d'=' -f2)
	mean=$(printf "%.12f" $mean)
	exp=$(cut -d' ' -f1 $test_directory/expected.txt)
	exp=$(printf "%.12f" $exp)

	#
	# check the mean value is within <tolerance> percentage of expected value
	#
	tolerance=0.01
	within_tolerance=$(echo "sqrt(($mean - $exp) * ($mean - $exp)) / $exp < $tolerance" | bc)
	if [ $within_tolerance -eq 1 ]; then
		result="PASS"
	else
		result="FAIL"
		exit_code=1
	fi
	printf "TEST %-30s: $result (computed: %.6f expected: %.6f)\n" $test_directory $mean $exp
done

exit $exit_code
