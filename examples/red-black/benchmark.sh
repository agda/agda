#!/bin/bash
# You'll need IEEE in your package database. If you happen to use stack
# and stack knows of its existence, you can do this:
agda2mlf -c --ghc-flag="-package-db `stack path --snapshot-pkg-db`" RedBlack.agda
# The malfunction backend has a hard-to-remember UI.
agda2mlf --mlf RedBlack.agda --compilemlf=RedBlackMlf -o RedBlack.mlf
ghc RedBlack.hs -main-is RedBlack -cpp -DRbUntyped    -o RbUntyped
ghc RedBlack.hs -main-is RedBlack -cpp -DRbTyped      -o RbTyped
ghc RedBlack.hs -main-is RedBlack -cpp -DRbTypedExist -o RbTypedExist
echo "Timing Agda backend"
time ./RedBlack     > /dev/null
echo "Timing Ocaml backend"
time ./RedBlackMlf  > /dev/null
echo "Timing haskell versions"
time ./RbUntyped    > /dev/null
time ./RbTyped      > /dev/null
time ./RbTypedExist > /dev/null



