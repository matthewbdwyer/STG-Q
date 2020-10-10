LLVM_PKGS="libllvm-10-ocaml-dev libllvm10 llvm-10 llvm-10-dev llvm-10-doc llvm-10-examples llvm-10-runtime"
OTHER_PKGS="uuid-dev libz-dev"

for p in $LLVM_PKGS $OTHER_PKGS
do
	sudo apt-get install $p
done
