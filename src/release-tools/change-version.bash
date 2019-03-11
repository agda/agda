#!/bin/bash

# Change Agda version in all files.

# Usage: From the repository root directory run
#   ./src/release-tools/change-version.bash old_version new_version

old_version="$1"
new_version="$2"

files='.ghci '
files+='Agda.cabal '
files+='doc/user-manual/conf.py '
files+='mk/versions.mk '
files+='src/data/emacs-mode/agda2-mode.el '
files+='src/data/emacs-mode/agda2-mode-pkg.el '
files+='src/size-solver/size-solver.cabal '
files+='test/interaction/Issue1244a.out '
files+='test/interaction/Issue1244b.out '

for i in $files; do
    sed -i "s/$old_version/$new_version/g" $i
done
