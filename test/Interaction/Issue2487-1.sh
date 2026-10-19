AGDA_BIN=$1

# generate interface without --safe (uses postulate)
$AGDA_BIN --no-guardedness --no-sized-types Issue2487-1.agda

# now reload with --safe; this should result in an error
$AGDA_BIN --safe Issue2487-1.agda
