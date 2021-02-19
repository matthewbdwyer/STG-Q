# 
# Utility script to cleanup STG-Q
#

if [ -z "$STGQ_HOME" ]; then
	echo "Environment variable STGQ_HOME is undefined"
	echo "Did you forget to source set_env_vars?"
	exit 1
fi

cd $STGQ_HOME
if [ -d build ]; then
	cd build
	make clean
fi

if [ -d "$STGQ_BIN" ]; then
	cd $STGQ_BIN
	rm -f stg*
	rm -f Quantify.sh
	rm -f comb
	rm -f res
fi
