#!/usr/bin/env bash
set -euo pipefail

agda="$1"
scratch=$(mktemp -d "${TMPDIR:-/tmp}/agda-issue-8608.XXXXXX")
trap 'rm -rf "$scratch"' EXIT
scratch=$(cd "$scratch" && pwd -P)

export Agda_datadir="$scratch/data"
export AGDA_DIR="$scratch/config"
mkdir "$Agda_datadir" "$AGDA_DIR" "$scratch/project"
cp Issue8608.agda "$scratch/project/"
cd "$scratch/project"

"$agda" --setup > "$scratch/setup.log" 2>&1 || { cat "$scratch/setup.log" >&2; exit 1; }
datadir=$("$agda" --print-agda-data-dir)

run_agda() {
  "$agda" --no-libraries --ignore-all-interfaces --color=never -i . "$@" \
    > "$scratch/check.log" 2>&1
}

builtin_sources="$scratch/builtin-sources"
for source in Agda/Primitive.agda Agda/Builtin/Bool.agda; do
  installed="$datadir/lib/prim/$source"
  target="$builtin_sources/$source"
  mkdir -p "$(dirname "$target")"
  mv "$installed" "$target"
  ln -s "$target" "$installed"
  test -L "$installed"
done
run_agda -i "$builtin_sources" Issue8608.agda || { cat "$scratch/check.log" >&2; exit 1; }
echo 'Installed builtin aliases resolved.'

real_dir="$scratch/ordinary-real"
link_dir="$scratch/ordinary-link"
copy_dir="$scratch/ordinary-copy"
mkdir "$real_dir" "$link_dir" "$copy_dir"
printf 'module Ordinary where\n' > "$real_dir/Ordinary.agda"
printf 'module Client where\nopen import Ordinary\n' > Client.agda
ln -s ../ordinary-real/Ordinary.agda "$link_dir/Ordinary.agda"
test -L "$link_dir/Ordinary.agda"

# Agda prepends each -i option, so the link comes first in lookup order.
run_agda -i "$real_dir" -i "$link_dir" Client.agda || { cat "$scratch/check.log" >&2; exit 1; }
test -f "$link_dir/Ordinary.agdai"
test ! -e "$real_dir/Ordinary.agdai"
echo 'Ordinary aliases resolved and the interface was written beside the link.'

cp "$real_dir/Ordinary.agda" "$copy_dir/Ordinary.agda"
status=0
run_agda -i "$copy_dir" -i "$real_dir" -i "$link_dir" Client.agda || status=$?
if [ "$status" -ne 42 ] || ! grep -Fq '[AmbiguousTopLevelModuleName]' "$scratch/check.log"; then
  cat "$scratch/check.log" >&2
  exit 1
fi
printf '  %s/Ordinary.agda\n' "$link_dir" "$copy_dir" > "$scratch/expected"
grep -E '^  .*/Ordinary\.agda$' "$scratch/check.log" > "$scratch/candidates"
diff -u "$scratch/expected" "$scratch/candidates" >&2
echo 'A distinct file still caused ambiguity.'
