#!/bin/sh

# Create CI on github for hTags using haskell-ci.

# Call me from the repository root.
if [ ! -f Agda.cabal ]; then
  echo "Error: invoke $0 from the project root"
  exit 1
fi

cabal_project=cabal.project

if [ -f $cabal_project ]; then
  echo "$cabal_project exists, cannot run"
  exit 1
fi

echo "packages: src/hTags/hTags.cabal" > $cabal_project

haskell-ci github \
  --github-action-name "Build hTags (cabal)" \
  --no-cabal-check \
  $cabal_project

#   --installed +all \
#   --installed -Cabal \

rm $cabal_project
