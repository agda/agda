# Test contributed by nad
AGDA_BIN=$1

# Should give no output
($AGDA_BIN -Werror --exact-split Issue2487-4.agda > /dev/null) && echo success

# Should output success (options changed)
($AGDA_BIN Issue2487-4.agda > /dev/null) && echo success

# Should not output anything (options changed again)
($AGDA_BIN -Werror --exact-split Issue2487-4.agda > /dev/null) && echo success
