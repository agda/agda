#!/bin/bash

set -e

echo "Installing Agda for the current user..."

echo "Writing to ~/.bashrc about the paths ..."

echo "export Agda_datadir="$PWD"/data">>~/.bashrc
echo "export PATH="$PWD"/bin:$PATH">>~/.bashrc

echo "The executable files should be executable ..."

chmod a+x ./bin/agda
chmod a+x ./bin/agda-mode

./bin/agda --version

echo "Initialize Emacs mode ..."

./bin/agda-mode setup
./bin/agda-mode compile

for prim in ./data/lib/prim/Agda/**/*.agda
do
    echo "Checking "$prim
    Agda_datadir=data ./bin/agda $prim
done

echo "Agda is supposed to be installed now."
echo ""
echo "You may use the following command to start using Agda right now:"
echo ""
echo "    source ~/.bashrc"
echo ""
