#!/bin/sh

# Andreas, 2023-09-01
# A shell script to check whether all Agda options are documented in the user manual.

# Options are documented in the following files of the user manual:
DOC="doc/user-manual/tools/command-line-options.rst doc/user-manual/tools/compilers.lagda.rst"

# 'agda --help' omits some options which are mentioned in the user manual:
HIDDEN_OPTIONS="--ignore-all-interfaces" # https://github.com/agda/agda/issues/3522#issuecomment-461010898

# We want to compute differences between the lists of existing and documented options.
# To use the 'comm' tool to this end, we need to store those in intermediate files.
TMPDIR=$(mktemp -d)
DOCOPTS=$TMPDIR/documented-options.txt
HELPOPTS=$TMPDIR/help-text-options.txt

# Documented options
grep -e '^.. option:: --\.*' $DOC | grep -oe '--[a-zA-Z-]\+' | sort | uniq > $DOCOPTS

# Existing options
(echo $HIDDEN_OPTIONS; $AGDA_BIN --help | grep -oe '--[a-zA-Z-]\+') | sort | uniq > $HELPOPTS

# Options that are documented but don't exist any longer.
REMOVED=$(comm -23 $DOCOPTS $HELPOPTS)
  ## -23 means only column 1 of output (additions in $DOCOPTS), not 2 and 3.

# Warn about non-existing options.
if [ "x$REMOVED" != "x" ]; then
  echo "Warning: The following options are not contained in the Agda help text but are still documentation in $DOC:"
  for i in $REMOVED; do
    echo "- $i"
  done
fi

# Options that exist but are undocumented.
UNDOCUMENTED=$(comm -13 $DOCOPTS $HELPOPTS)
  ## -13 means only column 2 of output (additions in $HELPOPTS), not 1 and 3.

# Print undocumented options and error out if we have one.
if [ "x$UNDOCUMENTED" != "x" ]; then
  echo "Error: The following Agda options lack a documentation in $DOC:"
  for i in $UNDOCUMENTED; do
    echo "- $i"
  done
  exit 1
fi
