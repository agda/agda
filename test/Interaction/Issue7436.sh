#!/bin/sh

# Andreas, 2024-09-02, issue #7436

AGDA=$1

# First build the interface files:
$AGDA Issue7436.agda --ignore-interfaces -v0

# The second invocation of agda, asking to compile, crashed with internal error,
# due to a dangling name that deadcode removal had introduced.
$AGDA Issue7436.agda --ghc --ghc-dont-call-ghc -v0
