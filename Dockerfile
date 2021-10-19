FROM ubuntu:20.04 

USER root

# STG-Q environment variables
ENV STGQ_HOME=/stgq
ENV STGQ_BIN=/stgq/bin
ENV STGQ_LIB=/stgq/lib
ENV PYSMT=/stgq/scripts
ENV QCORAL_HOME=/stgq/qcoral
ENV PATH="$PATH:/stgq/bin"

# Various base packages
RUN apt-get update -y && env DEBIAN_FRONTEND=noninteractive apt install --no-install-recommends -y scons bison flex g++ nasm sharutils gcc-multilib g++-multilib autoconf libelf-dev coreutils makeself cmake git unzip wget build-essential automake flex bison libglib2.0-dev openssl sudo fakeroot file ed texinfo 
RUN env DEBIAN_FRONTEND=noninteractive apt-get install -y lld-11 llvm-11 llvm-11-dev clang-11 llvm-11-runtime || sudo env DEBIAN_FRONTEND=noninteractive apt-get install -y lld llvm llvm-dev clang
RUN env DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends --reinstall ca-certificates

# Copy local copy
COPY . /stgq

# Install
WORKDIR /stgq 
RUN ./scripts/get-packages.sh
RUN ./scripts/register-clang-version.sh 11
RUN ./scripts/install_stgq.sh

ENTRYPOINT [ "/stgq/scripts/docker/stgq_entrypoint.sh" ]
CMD ["help"]



