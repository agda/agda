#!/bin/bash

# Change Agda version in all files.

# Usage: From the repository root directory run
#   ./src/release-tools/change-version.bash old_version new_version

old_version="$1"
new_version="$2"

files+='Agda.cabal '
files+='doc/user-manual/conf.py '
files+='mk/versions.mk '
files+='src/data/emacs-mode/agda2-mode.el '
files+='src/data/emacs-mode/agda2-mode-pkg.el '
files+='src/data/latex/agda.sty '
files+='src/size-solver/size-solver.cabal '
files+='test/Fail/Issue1963MagicWith.err  '
files+='test/Fail/Issue206.err '
files+='test/Fail/Issue2771.err '
files+='test/Fail/Issue2763.err '
files+='test/Fail/Issue530.err '
files+='test/Fail/MagicWith.err '
files+='test/interaction/Debug.out '
files+='test/interaction/Issue1244a.out '
files+='test/interaction/Issue1244b.out '
files+='test/interaction/Issue6261.out '

if [ "$2" == "" -o "$1" == "-h" -o "$1" == "--help" ]; then
  echo "Usage: $0 OLD NEW"
  echo "Replaces version string OLD by NEW in the following files:"
  for i in $files; do
    echo "- $i"
  done
  echo "Example: $0 2.6.4 2.6.3.20230913"
  exit 1
fi

for i in $files; do
    sed -i "s/$old_version/$new_version/g" $i
done
