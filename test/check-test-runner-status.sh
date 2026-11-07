#!/bin/sh

# A successful cleanup must not hide a failed test runner.
set -eu
cd "$(dirname "$0")/.."

# Isolate the generated helper file from any real test suite running in parallel.
test_workspace=$(mktemp -d "${TMPDIR:-/tmp}/agda-test-runner.XXXXXX")
trap 'rm -rf "$test_workspace"' 0
mkdir -p "$test_workspace/test/helpers/exec-tc"
cp Makefile "$test_workspace/Makefile"
cp -R mk "$test_workspace/mk"

for target in succeed accept-succeed fast-succeed; do
  for runner in false true; do
    test_status=0
    make --no-print-directory -C "$test_workspace" "$target" \
      AGDA_BIN=true AGDA_TESTS_BIN="$runner" \
      AGDA_FAST_BIN=true AGDA_FAST_TESTS_BIN="$runner" \
      AGDA_TESTS_OPTIONS= > "$test_workspace/output" 2>&1 || test_status=$?
    if { [ "$runner" = false ] && [ "$test_status" -eq 0 ]; } ||
       { [ "$runner" = true ] && [ "$test_status" -ne 0 ]; }; then
      cat "$test_workspace/output"
      echo "$target did not propagate the $runner runner's exit status" >&2
      exit 1
    fi
    if [ -e "$test_workspace/test/helpers/exec-tc/executables" ]; then
      echo "$target did not remove its generated helper file" >&2
      exit 1
    fi
  done
done
