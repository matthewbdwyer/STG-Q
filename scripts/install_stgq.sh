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
echo Debug real paver install
if [ -x "$REALPAVER" ]; then
	qcoral_vars="$QCORAL_HOME/qcoral/scripts/variables"
	if [ ! -f "$qcoral_vars" ]; then
		echo "Error: qcoral variable file not found: $qcoral_vars"
		exit 1
	fi

	# overwrite the environment variable REALPAVER in the file
	tmp=$(mktemp)
	grep -v REALPAVER $qcoral_vars > $tmp
	echo "REALPAVER=\"${REALPAVER}\"" >> $tmp
	mv $tmp $qcoral_vars

	echo "New qcoral variable file: "
	cat $qcoral_vars
else
	echo Error: realpaver executable not found
	exit 1
fi

# download qcoral
echo "============================================"
echo "Downloading pysmt: $PYSMT       "
echo "============================================"
cd $PYSMT
git clone https://github.com/soarlab/pysmt.git
cp $STGQ_HOME/target/fxp/conv_fxp_smt.py "$PYSMT/pysmt"

# if [ ! -d "$PYSMT/pysmt" ]; then

# 	git clone https://github.com/soarlab/pysmt.git
# 	cp $STGQ_HOME/target/fxp/conv_fxp_smt.py "$PYSMT/pysmt"
# fi

# Setup build directory
if [ -z "$STGQ_BUILD" ]; then
	STGQ_BUILD=$STGQ_HOME/build
else
	if [ ! -d $STGQ_BUILD ]; then
		mkdir -p $STGQ_BUILD
	fi
fi
if [ ! -d $STGQ_BUILD ]; then
	mkdir $STGQ_BUILD
fi

echo "=========================================="
echo "Ready to now build STG-Q from $STGQ_BUILD"
echo "=========================================="

cd $STGQ_BUILD
cmake $STGQ_HOME
make
make install

