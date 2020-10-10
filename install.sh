# 
# Utility script to install STG-Q
#

if [ -z "$STGQ_HOME" ]; then
	STGQ_HOME=$(dirname $(readlink -f "$0"))
fi

if [ -z "$STGQ_LIB" ]; then
	STGQ_LIB="$STGQ_LIB"/lib
	if [ ! -d "STGQ_LIB" ]; then
		mkdir "$STGQ_LIB"
	fi

fi

if [ -z "$STGQ_BIN" ]; then
	STGQ_BIN=$STGQ_LIB/bin
	if [ ! -d "STGQ_BIN" ]; then
		mkdir "$STGQ_BIN"
	fi
fi


cd $STGQ_HOME
./get-packages.sh
