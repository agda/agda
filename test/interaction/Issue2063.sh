#!/bin/sh

# The path to Agda (could also be a program on the PATH).
AGDA_BIN=$1

# The directory used to store output created by this script. Will be
# deleted.
BASE=Issue2063

########################################################################
# Create some Agda files

rm -rf $BASE
mkdir $BASE

cat > $BASE/Class.agda <<EOF
module $BASE.Class where

record R : Set₁ where
  field
    A : Set

open R ⦃ ... ⦄ public
EOF

cat > $BASE/Instance.agda <<EOF
module $BASE.Instance where

open import $BASE.Class

postulate
  instance
    i : R
EOF

cat > $BASE/Bug.agda <<EOF
module $BASE.Bug where

open import $BASE.Class
EOF

########################################################################
# Create some interface files

$AGDA_BIN $BASE/Instance.agda

########################################################################
# Load the main module (with caching turned on, if possible), add some
# more lines of code, and reload the module

FLAGS=$( ($AGDA_BIN --help | fgrep -- --caching > /dev/null) && \
         echo --caching)

LOAD="IOTCM \"$BASE/Bug.agda\" None Indirect \
        (Cmd_load \"$BASE/Bug.agda\" [\"%s\"])\n"

mkfifo $BASE/pipe

$AGDA_BIN --interaction < $BASE/pipe 2>&1 &

( printf "$LOAD" "$FLAGS"; \
  while [ ! -e $BASE/Bug.agdai ]; do \
    sleep 0.1; \
  done; \
  (printf "open import $BASE.Instance\nRejected : Set\nRejected = A\n" \
     >> $BASE/Bug.agda); \
  printf "$LOAD" "$FLAGS" \
) > $BASE/pipe

########################################################################
# Wait for Agda to complete, delete files

wait
rm -rf $BASE
