-- Jesper, 2018-05-14: constructor patterns of the parent clause can
-- now be replaced by a variable in the with clause.

open import Common.Prelude

f : List Nat → List Nat
f [] = []
f (x ∷ xs) with Set
f xs | p = xs
