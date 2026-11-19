#!/usr/bin/env bash
set -euo pipefail

# Andreas, 2020-08-11, issue #4828 reported by Robert Estelle.
# Test case adapted from his version.

agda="$1"
scratch=$(mktemp -d "${TMPDIR:-/tmp}/agda-issue-4828.XXXXXX")
trap 'rm -rf "$scratch"' EXIT

# Prepare this tree:
#
# agda-issue-4828.XXXXXX
# ├── src
# │   └── Issue4828.agda
# └── sym
#     └── Issue4828.agda -> ../src/Issue4828.agda

mkdir "$scratch/src" "$scratch/sym"
cp Issue4828.agda "$scratch/src/"
ln -s ../src/Issue4828.agda "$scratch/sym/Issue4828.agda"
test -L "$scratch/sym/Issue4828.agda"

if ! (cd "$scratch/sym" && "$agda" --no-libraries Issue4828.agda) \
    > "$scratch/agda.log" 2>&1; then
  cat "$scratch/agda.log" >&2
  exit 1
fi

if [[ ! -f "$scratch/sym/Issue4828.agdai" || -e "$scratch/src/Issue4828.agdai" ]]; then
  echo 'Expected Issue4828.agdai only beside the source symlink.' >&2
  exit 1
fi

echo 'The interface was written beside the source symlink.'
