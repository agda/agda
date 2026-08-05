#!/usr/bin/env bash

AGDA_BIN=$1

## A. File with wrong FOREIGN pragma

cat > Issue8647.agda <<EOF
{-# OPTIONS --caching #-}
open import Agda.Builtin.IO
open import Agda.Builtin.Unit

postulate
  exitFailure : IO ⊤

{-# FOREIGN GHC import System.Exit #-}
{-# COMPILE GHC exitFailure = Exit.exitFailure #-}

EOF

## Start interactive Agda but keep it running

# Create a unique named pipe
PIPE=$(mktemp -u)
mkfifo "$PIPE"

# Start Agda in the background reading from the pipe
# The "tail -f" trick keeps the pipe open so the command doesn't exit early
# Force tail's stdout to stay line-buffered
stdbuf -oL tail -f "$PIPE" | agda --interaction &
COMMAND_PID=$!

## Compile file interactively

cat >> "$PIPE" <<EOF
IOTCM "Issue8647.agda" None Indirect (Cmd_load "Issue8647.agda" [])
IOTCM "Issue8647.agda" None Indirect (Cmd_compile GHCNoMain "Issue8647.agda" [])
EOF

# Give Agda a brief moment to process the first block
sleep 1

## B. File with correct FOREIGN pragma

cat > Issue8647.agda <<EOF
{-# OPTIONS --caching #-}
open import Agda.Builtin.IO
open import Agda.Builtin.Unit

postulate
  exitFailure : IO ⊤

{-# FOREIGN GHC import qualified System.Exit as Exit #-}
{-# COMPILE GHC exitFailure = Exit.exitFailure #-}

EOF

## Compile file interactively

cat >> "$PIPE" <<EOF
IOTCM "Issue8647.agda" None Indirect (Cmd_load "Issue8647.agda" [])
IOTCM "Issue8647.agda" None Indirect (Cmd_compile GHCNoMain "Issue8647.agda" [])
EOF

# Allow final commands to output before closing
sleep 1

# Clean up and close Agda
kill $COMMAND_PID
rm "$PIPE"

## Call GHC again to make sure compilation succeeds

ghc MAlonzo/Code/Issue8647.hs

# The exit code of this script should be the one of this last command.
