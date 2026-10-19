{-# OPTIONS --allow-unsolved-metas --no-main #-}

open import Agda.Builtin.String
open import Agda.Builtin.Reflection

unquoteDecl = pragmaForeign "GHC" "x1 = 1"

HOLE : Set
HOLE = ?

unquoteDecl = pragmaForeign "GHC" "x2 = 2"

{-# FOREIGN GHC xs = x1 + x2 #-}
