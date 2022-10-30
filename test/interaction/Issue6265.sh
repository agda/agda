AGDA_BIN=$1

# This should work.
$AGDA_BIN --ignore-interfaces --no-libraries Issue6265.agda
# This should fail.
$AGDA_BIN --no-libraries --safe Issue6265.agda
