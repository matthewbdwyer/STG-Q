#
# Fetch packages for STG-Q
#

echo "====================================="
echo "Intalling required packages for STG-Q"
echo "====================================="

LLVM_PKGS="libllvm-11-ocaml-dev libllvm11 llvm-11 llvm-11-dev llvm-11-doc llvm-11-examples llvm-11-runtime"
OTHER_PKGS="uuid-dev libz-dev pkg-config libjsoncpp1 libjsoncpp-dev bc"
JAVA_PKGS="antlr4"
REALPAVER_PKGS="flex bison libfl-dev"

for p in $LLVM_PKGS $OTHER_PKGS $JAVA_PKGS $REALPAVER_PKGS
do
	sudo apt-get install -y $p
done
