#!/usr/bin/env bash

# Andreas, 2024-06-26, issue #7331:
# Handle permission error sensibly when looking for project root.

AGDA=${1}

mkdir -p Issue7331/dir             > /dev/null
touch Issue7331/dir/Issue7331.agda > /dev/null
pushd Issue7331/dir                > /dev/null

# Drop permissions for parent dir
chmod -r ..                        > /dev/null

${AGDA} --ignore-interfaces Issue7331.agda
result=$?

# Clean up
popd                               > /dev/null
chmod +r Issue7331                 > /dev/null
rm -rf Issue7331                   > /dev/null

exit $result
