#!/usr/bin/env bash

AGDA=$1

$AGDA --interaction --ignore-interfaces <<EOF
IOTCM "Issue4835/ModA.agda" None Indirect (Cmd_load "Issue4835/ModA.agda" [])
IOTCM "Issue4835/ModB.agda" None Indirect (Cmd_load "Issue4835/ModB.agda" [])
EOF

echo

# 8-byte big-endian module ID of ModA (= decimal 18141024170715853626).
# Must not contain "\x0a" (new line), otherwise "grep" will be confused.
MOD_ID=$'\xfb\xc1\xdd\x5e\x35\x4b\x33\x3a'

# Offset of compressed data in .agdai file. Actually 24, but "tail" starts
# counting at 1, not 0.
COMP_OFF=25

tail --bytes +${COMP_OFF} _build/*/agda/Issue4835/ModA.agdai | zcat | \
  grep --fixed-strings --binary "${MOD_ID}" >/dev/null

# ModA should contain its module ID.
if [ $? -ne 0 ]; then
  echo "Module ID not found in ModA."
  exit 1
fi

tail --bytes +${COMP_OFF} _build/*/agda/Issue4835/ModB.agdai | zcat | \
  grep --fixed-strings --binary "${MOD_ID}" >/dev/null

# ModB should not contain ModA's module ID.
if [ $? -eq 0 ]; then
  echo "Module ID found in ModB."
  exit 1
fi

exit 0
