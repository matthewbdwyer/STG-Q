set -e

cd $STGQ_HOME/test/tools
./run.sh

cd $STGQ_HOME/Test_Cases/
./run_tests.sh
