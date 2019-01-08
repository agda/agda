AGDA_BIN=$1

# generate interface without --safe
$AGDA_BIN --no-guardedness --no-sized-types Issue2487.agda

# now reload withh --safe; this should result in an error
$AGDA_BIN --safe Issue2487.agda
