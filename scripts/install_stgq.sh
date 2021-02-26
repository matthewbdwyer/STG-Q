# 
# Utility script to install STG-Q
#

if [ -z "$STGQ_HOME" ]; then
	echo "Environment variable STGQ_HOME is undefined"
	echo "Did you forget to source set_env_vars?"
	exit 1
fi

if [ ! -d "$STGQ_LIB" ]; then
	export STGQ_LIB="$STGQ_HOME"/lib
	if [ ! -d "STGQ_LIB" ]; then
		mkdir -p "$STGQ_LIB"
	fi

fi

if [ -z "$REALPAVER_HOME" ]; then
	REALPAVER_HOME=$STGQ_HOME/scripts/
fi

if [ ! -d "$REALPAVER_HOME" ]; then
	mkdir -p $REALPAVER_HOME
fi

# download antlr4
if [ ! -f "$STGQ_LIB/antlr-4.8-complete.jar" ]; then
	cd $STGQ_LIB
	wget https://www.antlr.org/download/antlr-4.8-complete.jar
fi

# download realpaver
echo "============================================"
echo "Installing realpaver: $REALPAVER_HOME     "
echo "============================================"
REALPAVER="$REALPAVER_HOME/realpaver-0.4/bin/realpaver"
if [ ! -x "$REALPAVER" ]; then
	cd $REALPAVER_HOME
	wget http://pagesperso.lina.univ-nantes.fr/~granvilliers-l/realpaver/src/realpaver-0.4.tar.gz
	tar -xzf realpaver*.tar.gz
	cd realpaver-0.4
	./configure
	make
fi

# download qcoral
echo "============================================"
echo "Installing qcoral: $QCORAL_HOME        "
echo "============================================"

if [ ! -d "$QCORAL_HOME" ]; then
	mkdir $QCORAL_HOME
	cd $QCORAL_HOME
	wget https://s3-us-west-2.amazonaws.com/qcoral/qcoral-fse-replication.tar.xz
	tar xf qcoral-fse-replication.tar.xz
fi

echo "============================================"
echo "Point qcoral to realpaver: $REALPAVER"
echo "============================================"
if [ -x "$REALPAVER" ]; then
	grep mateus $QCORAL_HOME/scripts/variables
	if [ $? -eq 0 ]; then
		echo Need to adjust realpaver path in qcoral/scripts/variables ...
		echo "Before"
		grep REALPAVER $QCORAL_HOME/qcoral/scripts/variables
		sed -i "s/mateus\/tools/$(whoami)\/STG-Q/g" $QCORAL_HOME/qcoral/scripts/variables
		echo "After"
		grep REALPAVER $QCORAL_HOME/qcoral/scripts/variables

	fi
else
	echo Error: realpaver executable not found
	exit 1
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

