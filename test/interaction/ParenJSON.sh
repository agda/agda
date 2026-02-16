#!/bin/sh

AGDA=$1
file="ParenJSON.agda"

$AGDA -v0 --interaction-json --color=never <<EOF
IOTCM "$file" None Indirect (Cmd_load "$file" [])
EOF
