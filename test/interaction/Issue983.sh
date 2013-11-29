
top=Issue983
bad=Issue983-Bad
lib=Issue983-Lib

pipe=$top.pipe

rm -f $pipe
mkfifo $pipe

# Forces the pipe to stay open. Otherwise it's closed by echo the first time we
# write to it.
sleep 2 > $pipe &

agda --interaction < $pipe 2>&1 &

function cmd {
  echo "IOTCM \"$2.agda\" None Indirect (Cmd_$1 \"$2.agda\" $3)" > $pipe
}

# The library is empty
printf "\n" > $lib.agda

# So this won't work
printf "open import $lib\n"        > $bad.agda
printf "Bad = $lib.NonExisting\n" >> $bad.agda

# Load the library.
cmd load $lib []

# Now load $top. This jumps to the error in $bad.
cmd load $top []

# Loading the highlighting info for $bad. This looks in the moduleToSource map
# for $lib which should not cause an internal error!
cmd load_highlighting_info $bad

sleep 0.1
rm -f $pipe $lib.agda $lib.agdai $bad.agda

