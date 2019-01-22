AGDA_BIN=$1

# A works with --safe
$AGDA_BIN --safe Issue2487/A.agda

# Works with --safe, imports A without rechecking
$AGDA_BIN --safe -v import.iface.options:4 Issue2487-2.agda

# Doesn't work without --safe, because A is rechecked (options changed)
$AGDA_BIN -v import.iface.options:4 Issue2487-2.agda
