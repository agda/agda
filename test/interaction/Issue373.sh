OBJECT_FILE=Imports/Nat.o

AGDA_BIN=$1

if [ -e "$OBJECT_FILE" ]; then
    rm "$OBJECT_FILE"
fi

echo 'IOTCM "Issue373.agda" None Indirect (Cmd_compile GHC "Issue373.agda" [])' | \
  $AGDA_BIN --interaction -v compile:0 2>&1

./Issue373
