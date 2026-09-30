#!/bin/sh

# Andreas, 2020-08-11, issue #4828 reported by Robert Estelle.
# Test case adapted from his version.

AGDA="$1 --no-libraries"
DIR=`mktemp -d -t issue-4828-`
# DIR="${PWD}/issue-4828"

# Prepare this tree:
#
# issue-4828
# ├── src
# │   └── Issue4828.agda
# └── sym
#     └── Issue4828.agda -> ../src/Issue4828.agda

rm -rf "${DIR}"
mkdir -p "${DIR}"/{src,sym}
echo 'module Issue4828 where' > "${DIR}"/src/Issue4828.agda
ln -s $DIR/src/Issue4828.agda "${DIR}"/sym/Issue4828.agda

# Run Agda on symlink
echo "Executing '$AGDA ${DIR}/sym/Issue4828.agda'"
( pushd "${DIR}"/sym > /dev/null && \
  $AGDA "${DIR}/sym/Issue4828.agda" && \
  popd > /dev/null )

# Debug printing
# tree "${DIR}"

# Test that .agdai file was placed next to symlink
# and not next to
test -f "${DIR}/sym/Issue4828.agdai"
test ! \( -f "${DIR}/src/Issue4828.agdai" \)

# Clean
rm -rf "${DIR}"
