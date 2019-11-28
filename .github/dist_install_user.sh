#!/bin/bash

set -e

echo "Installing Agda for the current user..."

echo "export Agda_datadir="$PWD"/data">>~/.bashrc
echo "export PATH="$PWD"/bin:$PATH">>~/.bashrc

./bin/agda-mode setup
./bin/agda-mode compile

./bin/agda --version

for prim in ./data/lib/prim/Agda/**/*.agda
do
    echo "Checking "$prim
    Agda_datadir=data ./bin/agda $prim
done

echo "Agda is supposed to be installed."
echo ""
echo "You may use the following command to start using Agda right now:"
echo ""
echo "    source ~/.bashrc"
echo ""
