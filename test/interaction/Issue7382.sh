#!/bin/sh

AGDA=$1

$AGDA -v0 --save-metas --ignore-interfaces Issue7382.agda
$AGDA -v0 --save-metas --compile --ghc-flag=-v0 Issue7382.agda
rm Issue7382 || true

# Problem was: Deserialization caused internal error.
