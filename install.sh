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

# download realpaver
echo "========================"
echo "Intalling realpaver     "
echo "========================"
REALPAVER="$STGQ_HOME/realpaver-0.4/bin/realpaver"
if [ ! -x "$REALPAVER" ]; then
	wget http://pagesperso.lina.univ-nantes.fr/~granvilliers-l/realpaver/src/realpaver-0.4.tar.gz
	tar -xzf realpaver*.tar.gz
	cd realpaver-0.4
	./configure
	make
fi

# download qcoral
echo "========================"
echo "Intalling qcoral        "
echo "========================"
cd $STGQ_HOME
if [ ! -d qcoral ]; then
	wget https://s3-us-west-2.amazonaws.com/qcoral/qcoral-fse-replication.tar.xz
	tar xf qcoral-fse-replication.tar.xz
fi

echo "========================="
echo "Point qcoral to realpaver"
echo "========================="
cd $STGQ_HOME
if [ -x "$REALPAVER" ]; then
	grep mateus qcoral/scripts/variables
	if [ $? -eq 0 ]; then
		echo Need to adjust realpaver path in qcoral/scripts/variables ...
		echo "Before"
		grep REALPAVER qcoral/scripts/variables
		sed -i "s/mateus\/tools/$(whoami)\/STG-Q/g" qcoral/scripts/variables
		echo "After"
		grep REALPAVER qcoral/scripts/variables

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

