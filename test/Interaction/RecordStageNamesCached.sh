#!/usr/bin/env bash
set -euo pipefail

agda="$1"

# Populate interfaces, then check local source access and imported privacy
# in a separate process using those interfaces.
"$agda" --no-default-libraries --ignore-interfaces -v0 RecordStageNamesCached/Client.agda
"$agda" --no-default-libraries --color=never --interaction <<'COMMANDS'
IOTCM "RecordStageNamesCached.agda" None Indirect (Cmd_load "RecordStageNamesCached.agda" [])
IOTCM "RecordStageNamesCached.agda" None Indirect (Cmd_infer_toplevel Normalised "R.1.F")
IOTCM "RecordStageNamesCached.agda" None Indirect (Cmd_infer_toplevel Normalised "Unused.0.unused")
IOTCM "RecordStageNamesCached.agda" None Indirect (Cmd_infer_toplevel Normalised "R.constructor")
IOTCM "RecordStageNamesCached/Client.agda" None Indirect (Cmd_load "RecordStageNamesCached/Client.agda" [])
IOTCM "RecordStageNamesCached/Client.agda" None Indirect (Cmd_infer_toplevel Normalised "Source.R.1.F")
IOTCM "RecordStageNamesCached/Client.agda" None Indirect (Cmd_infer_toplevel Normalised "Source.Public.F")
COMMANDS
