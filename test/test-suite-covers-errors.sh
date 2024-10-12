#!/bin/sh

# Andreas, end of August 2024
# A shell script to check whether all Agda errors are covered by the testsuite.

# We want to compute differences between the lists of existing and documented errors.
# To use the 'comm' tool to this end, we need to store those in intermediate files.
#
TMPDIR=$(mktemp -d)
HELPERRORS=$TMPDIR/help-text-errors.txt
ERRORS=$TMPDIR/test-suite-errors.txt
COVERED=$TMPDIR/covered-errors.txt

# Existing errors.
#
# Those are printed by `agda --help=error` at line beginnings and follow
# the camel-case convention, with at least two capital letters.
#
${AGDA_BIN:-agda} --help=error | sed -nr 's/^([A-Z][a-z\.]+[A-Z][A-Za-z\.]+).*/\1/p' | sort > $HELPERRORS

# Generic errors we do not need to cover by the testsuite.
#
cat > $ERRORS <<EOF
CustomBackendError
InternalError
NonFatalErrors
EOF

# Errors of the double checker which should be impossible.
#
cat >> $ERRORS <<EOF
HidingMismatch
QuantityMismatch
RelevanceMismatch
ShouldBePath
EOF

# Errors we currently do not cover by the testsuite (TODO!).
#
cat >> $ERRORS <<EOF
ContradictorySizeConstraint
Exec.ExeNotExecutable
Exec.ExeNotFound
Exec.ExeNotTrusted
FunctionTypeInSizeUniv
GeneralizeCyclicDependency
SplitError.CannotCreateMissingClause
SplitError.CosplitNoTarget
SplitError.GenericSplitError
Unquote.BlockedOnMeta
Unquote.UnquotePanic
EOF

# Errors covered by the testsuite.

# Testsuite golden value files.
#
FILES=$(find \( -name "*.err" -o -name "*.out" \))

# Names $NAME of errors are CamelCase and printed in that form:
#
#    ... error: [$NAME]
#
sed --silent --regexp-extended --expression='s/.*error: \[([A-Z][a-z\.]+[A-Z][A-Za-z\.]+)\].*/\1/p' $FILES | sort | uniq >> $ERRORS

sort $ERRORS | uniq > $COVERED

# Errors that exist but are not covered by the testsuite.
#
UNCOVERED=$(comm -13 $COVERED $HELPERRORS)
  ## -13 means only column 2 of output (additions in $HELPERRORS), not 1 and 3.

# Print uncovered errors and error out if we have one.
#
if [ "x$UNCOVERED" != "x" ]; then
  echo "Error: The following Agda errors are not covered by the testsuite:"
  for i in $UNCOVERED; do
    echo "- $i"
  done
  exit 1
fi
