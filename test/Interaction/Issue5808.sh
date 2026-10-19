#!/bin/sh

AGDA=$1
file="Issue5808.agda"

$AGDA -v0 --interaction-json --color=never <<EOF
IOTCM "$file" None Indirect (Cmd_load "$file" [])
IOTCM "$file" None Indirect (Cmd_refine 0 noRange "id1")
EOF
