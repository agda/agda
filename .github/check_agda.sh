#!/bin/bash

set -Eeu -o pipefail

export Agda_datadir=$PWD/data
export PATH=$PWD/bin:$PATH

if [[ "$OSTYPE" == "darwin"* ]]; then
  # See https://gitlab.haskell.org/ghc/ghc/-/issues/17418
  xattr -rc "${PWD}/bin"
fi

echo "The nightly version of Agda is"
agda --version

echo "Checking if Agda nightly is runnable on your system..."
find ./data/lib/prim -name "*.agda" -exec agda -v3 {} \;

if [ $? -eq 0 ]; then
  printf "\n🎉$(tput bold) Agda appears to work.\n"
  printf "Copy the following lines to your shell profile to access the nightly build, e.g. ~/.bashrc or ~/.zshrc$(tput sgr0)\n\n"
  printf 'export Agda_datadir=%q\n' "${PWD}/data"
  printf 'export PATH=%q:${PATH}\n' "${PWD}/bin"
else
  echo "Agda is not working. Bad luck." >&2
  exit 1
fi


