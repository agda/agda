#!/bin/sh

# Andreas, end of August 2024
# A shell script to check whether all Agda warnings are covered by the testsuite.

# We want to compute differences between the lists of existing and documented warnings.
# To use the 'comm' tool to this end, we need to store those in intermediate files.
#
TMPDIR=$(mktemp -d)
HELPWARNS=$TMPDIR/help-text-warnings.txt
BENIGNWARNS=$TMPDIR/benign-warnings.txt
ERRORS=$TMPDIR/errors.txt
COVERED=$TMPDIR/covered.txt

# Existing warnings.
#
# Those are printed by `agda --help=warning` at line beginnings and follow
# the camel-case convention, with at least two capital letters.
#
${AGDA_BIN:-agda} --help=warning | sed -nr 's/^([A-Z][a-z]+[A-Z][A-Za-z]+).*/\1/p' | sort > $HELPWARNS

# Warnings we do not need to cover by the testsuite.
#
cat > $BENIGNWARNS <<EOF
CustomBackendWarning
DeprecationWarning
DuplicateInterfaceFiles
LibUnknownField
EOF

# Warnings we ignore (e.g. that are still impossible).
#
cat >> $BENIGNWARNS <<EOF
EOF

# Warnings we currently do not cover by the testsuite (TODO!).
#
cat >> $BENIGNWARNS <<EOF
RewriteBlockedOnProblems
RewriteRequiresDefinitions
EOF

# Warnings covered by the testsuite.

# Testsuite golden value files.
#
FILES=$(find \( -name "*.warn" -o -name "*.err" -o -name "*.out" \))

# Names $WARNINGNAME of benign warnings are CamelCase and printed in this form:
#
#    ... warning: -W[no]$WARNINGNAME
#
sed --silent --regexp-extended --expression='s/.*warning: -W\[no\]([A-Z][a-z]+[A-Z][A-Za-z]+).*/\1/p' $FILES | sort | uniq >> $BENIGNWARNS

# Names $NAME of errors and error warnings are CamelCase and printed in that form:
#
#    ... error: [$NAME]
#
sed --silent --regexp-extended --expression='s/.*error: \[([A-Z][a-z]+[A-Z][A-Za-z]+)\].*/\1/p' $FILES | sort | uniq > $ERRORS

cat $BENIGNWARNS $ERRORS | sort | uniq > $COVERED

# Warnings that exist but are not covered by the testsuite.
#
UNCOVERED=$(comm -13 $COVERED $HELPWARNS)
  ## -13 means only column 2 of output (additions in $HELPWARNS), not 1 and 3.

# Print uncovered warnings and error out if we have one.
#
if [ "x$UNCOVERED" != "x" ]; then
  echo "Error: The following Agda warnings are not covered by the testsuite:"
  for i in $UNCOVERED; do
    echo "- $i"
  done
  exit 1
fi
