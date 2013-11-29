# This test tries to ensure that (certain) changes to OPTIONS pragmas
# are respected when a file is reloaded.

BASE=Issue641
FAIL="module $BASE where\nFoo : Set\nFoo = Set\n"
SUCCEED="{-# OPTIONS --type-in-type #-}\n$FAIL"
LOAD="IOTCM \"$BASE.agda\" None Indirect (Cmd_load \"$BASE.agda\" [])\n"

rm -f $BASE.pipe
mkfifo $BASE.pipe

agda --interaction < $BASE.pipe 2>&1 &

( (printf "$SUCCEED" > $BASE.agda); printf "$LOAD"; \
  while [ ! -e $BASE.agdai ]; do \
    sleep 0.1; \
  done; \
  rm $BASE.agdai; \
  (printf "$FAIL" > $BASE.agda); printf "$LOAD" \
) > $BASE.pipe

sleep 0.1
rm -f $BASE.pipe
