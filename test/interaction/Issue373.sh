OBJECT_FILE=Imports/Nat.o

if [ -e "$OBJECT_FILE" ]; then
    rm "$OBJECT_FILE"
fi

echo 'ioTCM "Issue373.agda" None (cmd_compile MAlonzo "Issue373.agda" [])' | \
  agda --interaction 2>&1

./Issue373
