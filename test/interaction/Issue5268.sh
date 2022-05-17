#!/usr/bin/env bash
set -Eeu -o pipefail

# Andreas, 2021-03-09, issue #5268.
# Symlinks causing trouble in termination error reporting.

AGDA="$1"
ROOT=$(pwd)
# BASE=`mktemp -d -t issue-5268-`
BASE=tmp-issue-5268
SRC=src/a
SYM="${BASE}"/sym
FILE=Issue5268.agda

# Prepare this tree:
#
# issue-5268
# ├── src
# │   ├── Main.agda-lib
# │   └── a
# │       └── Issue5268.agda
# └── sym -> src/a

rm -rf "${BASE}"
mkdir -p "${BASE}/${SRC}"
cd "${BASE}" > /dev/null
ln -s "${SRC}" sym
echo 'S : Set; S = S' > "${SRC}/${FILE}"
echo 'include: a' > "src/Main.agda-lib"
# No problem here:
# echo 'include: .' > "${SRC}/Main.agda-lib"
cd "${ROOT}" > /dev/null

# # Debug printing
# pwd
# tree "${BASE}"

# Run Agda on symlink
# cd sym
$AGDA --interaction <<EOF
IOTCM "${FILE}" None Indirect (Cmd_load "${SYM}/${FILE}" [])
EOF

# Clean
rm -rf "${BASE}"
