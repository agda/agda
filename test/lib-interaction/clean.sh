#!/usr/bin/env bash

# Andreas, 2014-05-21, adapted from ../fail/clean.sh

sed=$1

$sed -e 's/[^ (]*test.interaction.//g' \
  | $sed -e 's/[^ (]*lib.prim/agda-default-include-path/g' \
  | $sed -e 's/[^ (]*test.Common.//g' \
  | $sed -e 's/:[[:digit:]]\+:$//'

# EOF
