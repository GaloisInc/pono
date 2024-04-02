#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS=$DIR/../deps
MUST_DEPS=$DEPS/mustool/deps

MUST_VERSION=ed99aa14a4faf361504bf2f0c6ed0377b252f88c
Z3_VERSION=6cc52e04c3ea7e2534644a285d231bdaaafd8714

mkdir -p $DEPS
cd $DEPS

if [ ! -d "$DEPS/mustool" ]; then
    cd $DEPS
    git clone https://github.com/GaloisInc/mustool.git

    mkdir -p $MUST_DEPS
    cd $MUST_DEPS
    git clone https://github.com/Z3Prover/z3.git
    cd z3
    git checkout -f $Z3_VERSION
    ./configure --staticlib
    cd build
    make -j$(nproc)

    cd $MUST_DEPS/..
    git checkout -f $MUST_VERSION
    make libmust USESMT=YES
else
    echo "$DEPS/mustool already exists. If you want to rebuild, please remove it manually."
fi
