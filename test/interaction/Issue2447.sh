#!/bin/sh

AGDA=$1

$AGDA --interaction --color=never <<EOF
IOTCM "Issue2447.agda" None Indirect (Cmd_load "Issue2447.agda" ["--ignore-interfaces"])
IOTCM "Issue2447.agda" None Indirect (Cmd_load "Issue2447.agda" [])
EOF
