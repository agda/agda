#!/bin/sh

# Type-check the PLFA book, chapter by chapter.
#
# PLFA cannot be checked by a single Agda invocation (nor by
# `agda --build-library`): several chapters bind BUILTINs (e.g. BUILTIN NATURAL)
# that the standard library also binds, and a BUILTIN can only be bound once per
# Agda run.  So we run Agda once per chapter and collect the failures.
#
# Environment variables:
#   AGDA   the Agda command, including options (default: agda)

AGDA=${AGDA:-agda}

cd "$(dirname "$0")/plfa/src" || exit 1

failed=
for f in $(find plfa -name '*.lagda.md' | LC_ALL=C sort); do
  printf '=== %s\n' "$f"
  # shellcheck disable=SC2086
  if ! $AGDA "$f"; then
    failed="$failed $f"
  fi
done

if [ -n "$failed" ]; then
  echo "PLFA: the following chapters failed to type-check:"
  for f in $failed; do echo "  $f"; done
  exit 1
fi

echo "PLFA: all chapters type-check."
