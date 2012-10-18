# This test tries to ensure that (certain) changes to OPTIONS pragmas
# are respected when a file is reloaded.

BASE=Issue641
FAIL="module $BASE where\nFoo : Set\nFoo = Set\n"
SUCCEED="{-# OPTIONS --type-in-type #-}\n$FAIL"
LOAD="IOTCM \"$BASE.agda\" None (Cmd_load \"$BASE.agda\" [])\n"

rm -f $BASE.pipe
mkfifo $BASE.pipe

agda --interaction < $BASE.pipe 2>&1 &

( (printf "$SUCCEED" > $BASE.agda); printf "$LOAD"; \
  sleep 1; \
  (printf "$FAIL" > $BASE.agda); printf "$LOAD" \
) > $BASE.pipe

rm -f $BASE.pipe
