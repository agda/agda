#!/bin/sh

AGDA=$1

$AGDA --interaction --color=never <<EOF
IOTCM "Issue2447e.agda" None Indirect (Cmd_load "Issue2447e.agda" ["--ignore-interfaces"])
IOTCM "Issue2447e.agda" None Indirect (Cmd_load "Issue2447e.agda" [])
EOF
