#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS=$DIR/../deps

MUST_VERSION=e12212a752c5d55ed712c4d22e3c1ecc2f78fb7f

mkdir -p $DEPS

cd $DEPS
git clone https://github.com/GaloisInc/mustool.git
cd mustool
git checkout -f $MUST_VERSION
make libmust USESMT=YES
