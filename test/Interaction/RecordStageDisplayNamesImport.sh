#!/usr/bin/env bash
set -euo pipefail

agda="$1"

# Write fresh interfaces, then query them in a separate process without
# --ignore-interfaces. Stage qualifiers must survive serialization and imports.
"$agda" --no-default-libraries --ignore-interfaces -v0 RecordStageDisplayNamesImport.agda
"$agda" --no-default-libraries --color=never --interaction <<'EOF'
IOTCM "RecordStageDisplayNamesImport.agda" None Indirect (Cmd_load "RecordStageDisplayNamesImport.agda" [])
IOTCM "RecordStageDisplayNamesImport.agda" None Indirect (Cmd_infer_toplevel Normalised "Renamed.constructor")
IOTCM "RecordStageDisplayNamesImport.agda" None Indirect (Cmd_infer_toplevel Normalised "Source.Initial.constructor {A = Bool}")
IOTCM "RecordStageDisplayNamesImport.agda" None Indirect (Cmd_infer_toplevel Normalised "λ (r : Source.Outer) → Source.Outer.Inner.constructor {r}")
EOF
