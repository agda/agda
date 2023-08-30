#!/bin/sh

# Andreas, end of August 2023
# A shell script to check whether all Agda warnings are documented in the user manual.

# Warnings are documented in the following file of the user manual:
DOC=doc/user-manual/tools/command-line-options.rst

# We want to compute differences between the lists of existing and documented warnings.
# To use the 'comm' tool to this end, we need to store those in intermediate files.
TMPDIR=$(mktemp -d)
DOCWARNS=$TMPDIR/documented-warnings.txt
HELPWARNS=$TMPDIR/help-text-warnings.txt

# Documented warnings
sed -nr 's/^.. option:: ([A-Z][A-Za-z]*)/\1/p' $DOC | sort > $DOCWARNS

# Existing warnings
$AGDA_BIN --help=warning | sed -nr 's/^([A-Z][a-z]+[A-Z][A-Za-z]+).*/\1/p' | sort > $HELPWARNS

# Warnings that are documented but don't exist any longer.
REMOVED=$(comm -23 $DOCWARNS $HELPWARNS)
  ## -23 means only column 1 of output (additions in $DOCWARNS), not 2 and 3.

# Warn about non-existing warnings.
if [ "x$REMOVED" != "x" ]; then
  echo "Warning: The following warnings have been removed from Agda but are still documentation in $DOC:"
  for i in $REMOVED; do
    echo "- $i"
  done
fi

# Warnings that exist but are undocumented.
UNDOCUMENTED=$(comm -13 $DOCWARNS $HELPWARNS)
  ## -13 means only column 2 of output (additions in $HELPWARNS), not 1 and 3.

# Print undocumented warnings and error out if we have one.
if [ "x$UNDOCUMENTED" != "x" ]; then
  echo "Error: The following Agda warnings lack a documentation in $DOC:"
  for i in $UNDOCUMENTED; do
    echo "- $i"
  done
  exit 1
fi
