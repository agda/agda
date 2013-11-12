BASE=Issue720
LOAD="IOTCM \"$BASE.agda\" Interactive Direct (Cmd_load \"$BASE.agda\" [])\n"

rm -f $BASE.pipe
mkfifo $BASE.pipe

agda --interaction < $BASE.pipe 2>&1 &

rm -f $BASE.agdai
( printf "$LOAD"; \
  while [ ! -e $BASE.agdai ]; do \
    sleep 0.1; \
  done; \
  sleep 2; \  # On some systems time stamps may have a resolution of 1s.
  touch $BASE.agda; \
  printf "$LOAD" \
) > $BASE.pipe

rm -f $BASE.pipe
