#!/bin/bash
set -e
./amm scripts/namemap.sc $1
echo "Parsing $1"
build/bin/batchcheck $1
echo "Parsing $1 done"
