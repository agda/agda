#!/bin/sh

AGDA=$1

# Should print both "Checking" and "Finished"
$AGDA --interaction --trace-imports <<EOF
IOTCM "Issue6261.agda" None Indirect (Cmd_load "Issue6261.agda" [])
EOF

# Should print "Loading" because only compiled modules are affected
$AGDA --interaction --trace-imports=all <<EOF
IOTCM "Issue6261.agda" None Indirect (Cmd_load "Issue6261.agda" [])
EOF

# Should not print anything in the presence of -v0
$AGDA --interaction -v0 --trace-imports=all <<EOF
IOTCM "Issue6261.agda" None Indirect (Cmd_load "Issue6261.agda" [])
EOF
