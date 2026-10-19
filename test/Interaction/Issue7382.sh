#!/bin/sh

AGDA=$1

$AGDA Issue7382.agda -v0 --save-metas --ignore-interfaces
$AGDA Issue7382.agda -v0 --save-metas --ghc --ghc-dont-call-ghc

# Problem was: Deserialization caused internal error.
