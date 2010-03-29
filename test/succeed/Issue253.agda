{-# OPTIONS --universe-polymorphism --allow-unsolved-metas #-}
module Issue253 where

open import Common.Level

data Id l (X : Set l)(x : X) : X → Set where
  refl : Id l X x x

resp : (A B : Set _) → Id _ (Set _) A B → Set
resp  _ _ eq with eq
resp ._ _ eq | refl = Level

{-
An internal error has occurred. Please report this as a bug.
Location of the error: src/full/Agda/TypeChecking/Telescope.hs:51
-}