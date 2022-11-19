#!/bin/sh

AGDA=$1

$AGDA --interaction <<EOF
IOTCM "Issue6261.agda" None Indirect (Cmd_load "Issue6261.agda" [])
EOF

$AGDA --interaction --trace-imports=all <<EOF
IOTCM "Issue6261.agda" None Indirect (Cmd_load "Issue6261.agda" [])
EOF
