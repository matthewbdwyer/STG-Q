#!/bin/sh -e

case $1 in
	help)
		echo "usage: quantify <trace_dir>..."
		;;
	test)
		exec /stgq/Test_Cases/run_tests.sh
		;;
	quantify)
		shift
		echo "arguments to quantify: $*"
		exec Quantify.sh $*
		;;
	*)
		echo "Unsupported command: $*"
		exit 1
		;;
esac

exit 0
