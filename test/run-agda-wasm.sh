#!/usr/bin/env sh

# A wrapper script that runs Agda with wasmtime, for use in the test scripts.

set -eu
exec wasmtime --env "PATH=$PATH" --env "PWD=$PWD" --env "HOME=$HOME" \
    --dir "/" --argv0 agda \
    "$AGDA_WASM" "$@"
