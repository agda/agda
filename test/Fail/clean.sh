#!/bin/bash

sed=$1

$sed -e 's/[^ (]*test.Fail.//g' \
  | $sed -e 's/[^ (]*lib.prim/agda-default-include-path/g' \
  | $sed -e 's/[^ (]*test.Common.//g' \
  | $sed -e 's/\\/\//g' \
  | $sed -e 's/:[[:digit:]]\+:$//' \
  | $sed -e "s/\xe2\x80\x9b\|\xe2\x80\x99\|\xe2\x80\x98\|\`/'/g"

