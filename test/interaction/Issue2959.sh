#!/bin/sh

AGDA=$1

$AGDA --interaction --caching --no-libraries --ignore-interfaces <<EOF
IOTCM "Issue2959.agda" None Indirect (Cmd_load "Issue2959.agda" [])
IOTCM "Issue2959.agda" None Indirect (Cmd_make_case 0 noRange "")
IOTCM "Issue2959.agda" None Indirect (Cmd_load "Issue2959.agda" [])
IOTCM "Issue2959.agda" None Indirect (Cmd_make_case 0 noRange "")
EOF
