#!/bin/sh

AGDA=$1

$AGDA --interaction <<EOF
IOTCM "Issue2447c.agda" None Indirect (Cmd_load "Issue2447c.agda" ["--ignore-interfaces"])
IOTCM "Issue2447c.agda" None Indirect (Cmd_load "Issue2447c.agda" [])
EOF
