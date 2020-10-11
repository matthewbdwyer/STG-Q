#!/bin/bash

cd $(dirname $(readlink -f "$0"))

#
# set the tolerance (%) by which the computed STG score in a test
# can deviate from the expected score
#
tolerance=0.01

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
	expected=$(cut -d' ' -f1 $test_directory/expected.txt)
	expected=$(printf "%.12f" $expected)

	#
	# check the mean value is within <tolerance> percentage of expected value
	#
	within_tolerance=$(echo "sqrt(($mean - $expected) * ($mean - $expected)) / $expected < $tolerance" | bc)
	if [ $within_tolerance -eq 1 ]; then
		result="PASS"
	else
		result="FAIL"
		exit_code=1
	fi
	printf "TEST %-30s: $result (computed: %.6f expected: %.6f)\n" $test_directory $mean $expected
done

exit $exit_code
