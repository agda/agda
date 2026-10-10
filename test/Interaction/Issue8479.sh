#!/usr/bin/env bash

AGDA_BIN=$1

rm -f Issue8479/*.agdai
"$AGDA_BIN" --no-default-libraries --color=never -i . -i .. --interaction <<'EOF'
IOTCM "Issue8479.agda" NonInteractive Direct (Cmd_load "Issue8479.agda" [])
EOF
