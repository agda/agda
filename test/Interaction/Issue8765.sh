#!/usr/bin/env bash

AGDA_BIN=$1

rm -f Issue8765/*.agdai
"$AGDA_BIN" --no-default-libraries -i . -i .. -v0 Issue8765/M2.agda
"$AGDA_BIN" --no-default-libraries --color=never -i . -i .. --interaction <<'EOF'
IOTCM "Issue8765.agda" NonInteractive Direct (Cmd_load "Issue8765.agda" [])
EOF
