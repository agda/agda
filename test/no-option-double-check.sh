#!/bin/sh
# Andreas, 2023-09-03, error on '--double-check' in 'Succeed' and 'Fail' suites.
#
# No test in Succeed or Fail should turn on --double-check manually.
# This would override the control by the test suite runners.
#
# Run this script from the Agda repo root.

# On macOS, 'grep -R' is a magnitude faster than 'find -exec grep'.
BAD=$(grep -R -l -e '--double-check' --include=\*.{agda,lagda,lagda.\*,flags} test/Succeed test/Fail)

if [ "x$BAD" != "x" ]; then
  echo "Error: the following files supply the --double-check option which is already given by the test runner."
  for i in $BAD; do
    echo "- $i"
  done
  echo "Please remove this option from these files so that it can be controlled by the runner."
  exit 1
fi
