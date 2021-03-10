#!/bin/sh

# Create CI on github for hTags using haskell-ci.

cidir=.github/workflows
srcdir=src/hTags
target=$cidir/hTags.yml
patchfile=$srcdir/github-ci.patch

if [ "x$1" != "x" ]; then
  echo "Invoke $0 from the project root to generate CI for hTags"
  echo "INFO: command for patch creation:"
  echo "INFO: diff $target $cidir/hTags-patched.yml > $patchfile"
  exit 1
fi

# Call me from the repository root.
if [ ! -f Agda.cabal ]; then
  echo "Error: invoke $0 from the project root"
  exit 1
fi

# In order to build CI with haskell-ci in a subdirectory
# we need to go via cabal.project.

cabal_project=cabal.project

# Make sure we do not destroy a cabal.project file.

if [ -f $cabal_project ]; then
  echo "$cabal_project exists, cannot run"
  exit 1
fi

# Create cabal.project, run haskell-ci, delete cabal.project

echo "packages: src/hTags/hTags.cabal" > $cabal_project

haskell-ci github \
  --github-action-name "Build hTags (cabal)" \
  --no-cabal-check \
  $cabal_project

#   --installed +all \
#   --installed -Cabal \

rm $cabal_project

# Post-processing: move result to hTags.yml and patch

mv $cidir/haskell-ci.yml $target
patch --input $patchfile $target

# EOF
