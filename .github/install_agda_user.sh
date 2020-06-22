#!/bin/bash

set -e

echo "Installing Agda for the current user..."

echo "Writing to ~/.bashrc about the paths ..."

echo "export Agda_datadir="$PWD"/data">>~/.bashrc
echo "export PATH="$PWD"/bin:$PATH">>~/.bashrc

export Agda_datadir=$PWD/data
export PATH=$PWD/bin:$PATH

echo "The executable files should be executable ..."

chmod a+x ./bin/agda
chmod a+x ./bin/agda-mode
chmod a+x ./bin/size-solver

agda --version

for prim in ./data/lib/prim/Agda/**/*.agda
do
    echo "Checking "$prim
    agda $prim
done

echo "Agda is supposed to be installed now."
echo ""
echo "You may open another terminal session, or use the"
echo "following command to start using Agda right now:"
echo ""
echo "    source ~/.bashrc"
echo ""
