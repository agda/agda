#!/bin/sh

# Andreas, September 2024
# Call this script from the project root.

file=$(grep -le '\<RecursiveDo\>' Agda.cabal)
files=$(grep -Rle '\<RecursiveDo\>' src/full --include="*.hs")

if [ -n "$(echo $file $files)" ]; then
  echo "LANGUAGE RecursiveDo is not permitted in this code base (#7303), but found in the following files:"
  for i in $file $files; do
    echo "- $i"
  done
  exit 1
fi
