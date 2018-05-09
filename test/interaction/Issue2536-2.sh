#!/bin/sh

AGDA=$1

LC_CTYPE=C $AGDA --interaction --ignore-interfaces <<EOF
IOTCM "Issue2536-2.lagda" None Indirect (Cmd_load "Issue2536-2.lagda" [])
EOF
