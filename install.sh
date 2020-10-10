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


# install other package
cd $STGQ_HOME
./get-packages.sh

# download antlr4
if [ ! -f "$STGQ_LIB/antlr-4.8-complete.jar" ]; then
	cd $STGQ_LIB
	wget https://www.antlr.org/download/antlr-4.8-complete.jar
	cd -
fi
