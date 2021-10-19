#!/bin/bash

test_dir=$(dirname $(readlink -f "$0"))
cd $test_dir

#
# set the tolerance (%) by which the computed STG score in a test
# can deviate from the expected score
#
tolerance=0.05

exit_code=0
mean=0
for testdir in `ls`
do
	# skip non-directories
	if [ ! -d $testdir ]; then
		continue
	fi

	# no expected.txt file, so skip
	if [ ! -f $testdir/expected.txt ]; then
		printf "TEST %-30s: SKIP (No expected.txt found)\n" $testdir
		continue
	fi

	# output of quantify: [qCORAL:results] samples=5000000, mean=2.499708e-01, variance=3.749708e-08, time=4.682822, stdev=1.936416e-04
	if [ ! -f "$test_dir/$(basename "$testdir")/dict.json" ]; then
		mean=$($STGQ_HOME/target/qcoral/Quantify.sh $test_dir/$(basename "$testdir") 2>/dev/null | grep mean | cut -d',' -f2 | cut -d'=' -f2)
	else
		mean=$($STGQ_HOME/target/qcoral/Quantify.sh $test_dir/$(basename "$testdir") $test_dir/$(basename "$testdir")/dict.json 2>/dev/null | grep mean | cut -d',' -f2 | cut -d'=' -f2)
	fi

	mean=$(printf "%.12f" $mean)
	expected=$(cut -d' ' -f1 $testdir/expected.txt)
	expected=$(printf "%.12f" $expected)

	#
	# check the mean value is within <tolerance> percentage of expected value
	#
	within_tolerance=$(echo "scale=4;sqrt(($mean - $expected) * ($mean - $expected)) / $expected < $tolerance" | bc)
	
	if [ $within_tolerance -eq 1 ]; then
		result="PASS"
	else
		result="FAIL"
		exit_code=1
	fi
	printf "TEST %-30s: $result (computed: %.6f expected: %.6f)\n" $testdir $mean $expected
done

exit $exit_code
