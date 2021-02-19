# 
# Utility script to install STG-Q
#

if [ -z "$STGQ_HOME" ]; then
	echo "Environment variable STGQ_HOME is undefined"
	echo "Did you forget to source set_env_vars?"
	exit 1
fi

if [ ! -d "$STGQ_LIB" ]; then
	STGQ_LIB="$STGQ_HOME"/lib
	if [ ! -d "STGQ_LIB" ]; then
		mkdir "$STGQ_LIB"
	fi

fi

echo "========================"
echo "Ready to now build STG-Q"
echo "========================"
cd $STGQ_HOME
if [ ! -d build ]; then
	mkdir build
fi
cd build
cmake ..
make
make install

