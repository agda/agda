#!/usr/bin/env bash

AGDA=${1}

cd Issue5250 > /dev/null
rm -rf _build > /dev/null

${AGDA} --no-default-libraries Issue5250.agda

sed -e 's/flags:/flags: -Wall/' Issue5250.agda-lib > Issue5250.agda-lib.tmp &&
  mv Issue5250.agda-lib.tmp Issue5250.agda-lib

${AGDA} --no-default-libraries Issue5250.agda

sed -e 's/flags: -Wall/flags:/' Issue5250.agda-lib > Issue5250.agda-lib.tmp &&
  mv Issue5250.agda-lib.tmp Issue5250.agda-lib
