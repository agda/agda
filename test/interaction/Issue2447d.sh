#!/bin/sh

AGDA=$1

$AGDA --interaction <<EOF
IOTCM "Issue2447d.agda" None Indirect (Cmd_load "Issue2447d.agda" ["--ignore-interfaces"])
IOTCM "Issue2447d.agda" None Indirect (Cmd_load "Issue2447d.agda" [])
EOF
