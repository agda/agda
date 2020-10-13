#!/usr/bin/env bash
set -Eeu -o pipefail

AGDA="$1"

ISSUE=Issue2937

echo 'Loading WithUnicode and then NonUnicode'
$AGDA --interaction --ignore-interfaces -vimport.iface.options:5 <<EOF
IOTCM "${ISSUE}/WithUnicode.agda" None Indirect (Cmd_load "${ISSUE}/WithUnicode.agda" [])
IOTCM "${ISSUE}/NoUnicode.agda" None Indirect (Cmd_load "${ISSUE}/NoUnicode.agda" [])
EOF

echo '****************************************'
echo 'Loading NoUnicode and then Unicode'

$AGDA --interaction --ignore-interfaces -vimport.iface.options:5 <<EOF
IOTCM "${ISSUE}/NoUnicode.agda" None Indirect (Cmd_load "${ISSUE}/NoUnicode.agda" [])
IOTCM "${ISSUE}/WithUnicode.agda" None Indirect (Cmd_load "${ISSUE}/WithUnicode.agda" [])
EOF
