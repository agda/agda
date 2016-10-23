
AGDA_BIN=$1
top=Issue1232
lib=Issue1232/All
mod=Issue1232.List

pipe=$top.pipe

rm -f $pipe
mkfifo $pipe

# Forces the pipe to stay open. Otherwise it's closed by echo the first time we
# write to it.
sleep 2 > $pipe &
SLEEP_PID=$!

$AGDA_BIN --interaction < $pipe 2>&1 &

function cmd {
  echo "IOTCM \"$2.agda\" None Indirect (Cmd_$1 \"$2.agda\" $3)" > $pipe
}

# Set up the test file
printf "import $mod" > $top.agda

# Check the library
$AGDA_BIN $lib.agda --ignore-interfaces

# Load the test file
cmd load $top []

# Make sure it's loaded
sleep 0.1

# Now change the test
printf "\n" >> $top.agda

# and reload
cmd load $top []

sleep 0.1
rm -f $pipe $top.agda $top.agdai

# Free the pipe to prevent weird errors on nfs file systems
kill $SLEEP_PID
wait $SLEEP_PID 2>/dev/null

# Restore the test file (it needs to be in the repo for the Makefile to work)
printf "\n" > $top.agda

