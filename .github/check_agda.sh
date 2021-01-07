#!/bin/bash

set -Eeu -o pipefail

export Agda_datadir=$PWD/data
export PATH=$PWD/bin:$PATH

if [[ "$OSTYPE" == "darwin"* ]]; then
  # See https://gitlab.haskell.org/ghc/ghc/-/issues/17418
  chmod +w "${PWD}"/lib/*
  xattr -rc "${PWD}/bin"
  xattr -rc "${PWD}/lib"
  chmod -w "${PWD}"/lib/*
fi

agda --version

echo "\n$(tput bold)Checking if Agda nightly is runnable on your system...$(tput sgr0)"
find ./data/lib/prim -name "*.agda" -exec agda -v2 {} \;

if [ $? -eq 0 ]; then
  printf "\n🎉$(tput bold) Agda is working.\n"
  printf "Copy the following lines to your shell profile to access the nightly build, e.g. ~/.bashrc or ~/.zshrc$(tput sgr0)\n\n"
  printf 'export Agda_datadir=%q\n' "${PWD}/data"
  printf 'export PATH=%q:${PATH}\n' "${PWD}/bin"
else
  echo "Agda is not working. Bad luck." >&2
  exit 1
fi
