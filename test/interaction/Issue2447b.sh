#!/bin/sh

AGDA=$1

$AGDA --interaction --color=never <<EOF
IOTCM "Issue2447b.agda" None Indirect (Cmd_load "Issue2447b.agda" ["--ignore-interfaces"])
IOTCM "Issue2447b.agda" None Indirect (Cmd_load "Issue2447b.agda" [])
EOF
