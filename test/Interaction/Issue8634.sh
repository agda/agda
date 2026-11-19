#!/usr/bin/env sh

AGDA=$1

# On some systems the cd command can print a path, so output is
# redirected to /dev/null.
cd Issue8634 > /dev/null
rm -rf _build
$AGDA --color=never --interaction <<EOF
IOTCM "Issue8634.agda" None Indirect (Cmd_load "Issue8634.agda" [])
EOF
