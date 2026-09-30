AGDA_BIN=$1

# Everything works
echo "== Good run"
echo "== Should check Top -> B -> D -> C"
$AGDA_BIN Issue5357.agda -v1 --ignore-interfaces

# Make D fail
cp Imports/Issue5357-D.agda Imports/Issue5357-GoodD.agda
cp Imports/Issue5357-BadD.agda Imports/Issue5357-D.agda

# Should not recheck D multiple times
echo "== Failing run"
echo "== Should check D -> error"
$AGDA_BIN Issue5357.agda -v1

# Restore D
mv Imports/Issue5357-GoodD.agda Imports/Issue5357-D.agda
