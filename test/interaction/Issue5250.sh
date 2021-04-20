#!/usr/bin/env bash

AGDA=${1}

cd Issue5250 > /dev/null

${AGDA} --no-default-libraries Issue5250.agda

sed -ri -e 's/flags:/flags: -Wall/' Issue5250.agda-lib 

${AGDA} --no-default-libraries Issue5250.agda

sed -ri -e 's/flags: -Wall/flags:/' Issue5250.agda-lib
