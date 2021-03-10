#!/bin/bash

set -e

echo "Installing Agda's Emacs mode..."

./bin/agda-mode setup
./bin/agda-mode compile

echo "Done."
