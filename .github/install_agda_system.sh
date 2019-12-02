#!/bin/bash

set -e

echo "Installing Agda for all users..."

echo "Writing to /etc/environment about the paths ..."

echo "export Agda_datadir="$PWD"/data">>/etc/environment

export Agda_datadir=$PWD/data

echo "The executable files should be executable ..."

chmod 777 ./bin/agda
chmod 777 ./bin/agda-mode
chmod 777 ./bin/size-solver

echo "Copying executables ..."

cp ./bin/* /usr/bin

agda --version

## Don't produce files with sudo access

echo "Agda is supposed to be installed now."
echo ""
echo "You may logout and re-login, or use the"
echo "following command to start using Agda right now:"
echo ""
echo "    source /etc/environment"
echo ""
