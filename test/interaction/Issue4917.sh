#!/usr/bin/env bash

AGDA=$1

$AGDA --interaction --ignore-interfaces --verbose tc:5 <<EOF | grep "Checking D"
IOTCM "Issue4917.agda" None Indirect (Cmd_load "Issue4917.agda" [])
IOTCM "Issue4917.agda" None Indirect (Cmd_load "Issue4917.agda" [])
EOF
