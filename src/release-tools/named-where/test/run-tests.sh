#!/usr/bin/env sh

# Run named-where.py on the test corpus and compare with `expected.txt`.

set -e
cd "$(dirname "$0")"
../named-where.py --all --column . > actual.txt
if diff -u expected.txt actual.txt; then
    rm -f actual.txt
    echo "named-where: all tests passed"
else
    echo "named-where: FAILED (see actual.txt)" >&2
    exit 1
fi
