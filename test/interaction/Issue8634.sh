#!/usr/bin/env sh

AGDA=$1

cd Issue8634
rm -rf _build
$AGDA --interaction <<EOF
IOTCM "Issue8634.agda" None Indirect (Cmd_load "Issue8634.agda" [])
EOF
