# Andreas, 2016-07-29, issue #2122

AGDA_BIN=$1

$AGDA_BIN --library-file=GARBAGE Issue2122.agda

# should complain about non-existent library file

# EOF
