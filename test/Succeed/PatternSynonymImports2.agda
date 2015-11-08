module PatternSynonymImports2 where

open import PatternSynonyms hiding (test)
open import PatternSynonymImports

myzero' = z
myzero'' = myzero

list2 : List _
list2 = 1 ∷ []

test : ℕ → ℕ
test myzero = 0
test sz     = 1
test (ss x) = x
