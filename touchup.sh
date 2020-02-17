#!/bin/bash -ui

~/.cabal/bin/hlint --refactor $1 --refactor-options="-XLambdaCase -XMultiWayIf -XRankNTypes" > "$1"X && diff $1 "$1"X 
if [ $? -eq 1 ]; then
  mv -i "$1X" $1
fi
rm -f "$1"X

