#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS=$DIR/../deps

MUST_VERSION=aea91490e4cd25b9356c2e2dfd53f90b956f827e

mkdir -p $DEPS

cd $DEPS
git clone https://github.com/GaloisInc/mustool.git
cd mustool
git checkout -f $MUST_VERSION
make libmust USESMT=YES
