#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS=$DIR/../deps

MUST_VERSION=f533a59d895707bebe5f829c7d0d35c9a91a163a

mkdir -p $DEPS
cd $DEPS

if [ ! -d "$DEPS/mustool" ]; then
    cd $DEPS
    git clone https://github.com/GaloisInc/mustool.git
    cd mustool
    git checkout -f $MUST_VERSION
    make libmust USESMT=YES -j$(nproc)
else
    echo "$DEPS/mustool already exists. If you want to rebuild, please remove it manually."
fi
