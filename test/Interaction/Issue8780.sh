#!/usr/bin/env sh

# Andreas, 2026-09-29, issue #8780
# Reported and reproducer by Ulrik Buchholtz
# Needs a specialized test because profiling data would end up in the golden value
# if it was just a test/Fail.

AGDA=$1

# This should fail with an ordinary type error, not crash with an internal error.
$AGDA --profile=modules Issue8780.agda > /dev/null
# NB: swallow output since it contains profiling data.

EXIT_CODE=$?
if [ $EXIT_CODE == 42 ]; then
  echo "Regular error.  That's expected."
  echo "OK"
elif [ $EXIT_CODE == 120 ]; then
  # Fail if Agda exited with 120 (internal error)
  echo "Internal error.  That's bad."
  echo "FAIL"
  exit 1
else
  echo "Unexpected exit code from Agda.  That's bad."
  echo "Needs to be investigated!"
  echo "FAIL"
  exit 1
fi
