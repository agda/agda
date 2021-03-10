#!/bin/bash -ui

if [ -f "$1" ]; then
        ~/.cabal/bin/hlint --refactor "$1" --refactor-options="-XLambdaCase -XMultiWayIf -XRankNTypes" > "$1"X && diff "$1" "$1"X
        if [ $? -eq 1 ]; then
          mv -i "$1X" "$1"
        fi
        rm -f "$1"X
else
        echo "File does not exist: $1"
fi
