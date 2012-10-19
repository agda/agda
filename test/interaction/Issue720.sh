BASE=Issue720
LOAD="IOTCM \"$BASE.agda\" Interactive Direct (Cmd_load \"$BASE.agda\" [])\n"

rm -f $BASE.pipe
mkfifo $BASE.pipe

agda --interaction < $BASE.pipe 2>&1 &

( printf "$LOAD"; \
  sleep 1; \
  touch $BASE.agda; \
  printf "$LOAD" \
) > $BASE.pipe

rm -f $BASE.pipe
