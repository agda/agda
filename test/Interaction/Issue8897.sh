#!/usr/bin/env bash
set -euo pipefail

agda="$1"
scratch=$(mktemp -d "${TMPDIR:-/tmp}/agda-issue-8897.XXXXXX")
trap 'rm -rf "$scratch"' EXIT

export Agda_datadir="$scratch/data"
export AGDA_DIR="$scratch/config"
mkdir "$Agda_datadir" "$AGDA_DIR"
cp Issue8897.agda "$scratch/"

"$agda" --setup > "$scratch/setup.log" 2>&1 || { cat "$scratch/setup.log" >&2; exit 1; }
datadir=$("$agda" --print-agda-data-dir)

check_import() {
  if (cd "$scratch" && "$agda" --no-libraries --ignore-all-interfaces Issue8897.agda) \
      > "$scratch/check.log" 2>&1; then
    echo "Builtin import passed with $1."
  else
    cat "$scratch/check.log" >&2
    return 1
  fi
}

check_import 'a plain data directory'

mv "$datadir/lib" "$scratch/lib"
ln -s "$scratch/lib" "$datadir/lib"
test -L "$datadir/lib"
check_import 'a symlinked lib directory'
rm "$datadir/lib"
mv "$scratch/lib" "$datadir/lib"

mv "$datadir/lib/prim" "$scratch/prim"
ln -s "$scratch/prim" "$datadir/lib/prim"
test -L "$datadir/lib/prim"
check_import 'a symlinked prim directory'
