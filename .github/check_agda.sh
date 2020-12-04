#!/bin/bash

set -e

export Agda_datadir=$PWD/data
export PATH=$PWD/bin:$PATH

if [[ "$OSTYPE" == "darwin"* ]]; then
  # See https://gitlab.haskell.org/ghc/ghc/-/issues/17418
  xattr -rc $PWD/bin
fi

echo "The nightly version of Agda is"
agda --version

echo "Checking if Agda nightly is runnable on your system..."
for prim in ./data/lib/prim/Agda/**/*.agda
do
    echo "Checking "$prim
    agda -v 2 $prim
done

if [ $? == 0 ];
then
  printf "$(tput bold)Agda appears to work.\nCopy the following lines to your shell profile to access the nightly build, e.g. ~/.bashrc\n"
  echo "export Agda_datadir="$PWD"/data"
  echo "export PATH="$PWD"/bin:\$PATH"
else
  echo "Agda is not working. Bad luck."
fi

