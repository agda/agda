#!/usr/bin/env bash

AGDA_BIN=$1

# Write Issue8905.agdai, so that the interaction below loads from it.
rm -f Issue8905.agdai
"$AGDA_BIN" --no-default-libraries -v0 Issue8905.agda
"$AGDA_BIN" --no-default-libraries --color=never --interaction <<'EOF'
IOTCM "Issue8905.agda" None Indirect (Cmd_load "Issue8905.agda" [])
IOTCM "Issue8905.agda" None Indirect (Cmd_infer_toplevel AsIs "D")
IOTCM "Issue8905.agda" None Indirect (Cmd_infer_toplevel AsIs "d")
IOTCM "Issue8905.agda" None Indirect (Cmd_infer_toplevel AsIs "D → D")
EOF
rm -f Issue8905.agdai
