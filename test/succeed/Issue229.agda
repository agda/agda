{-# OPTIONS --universe-polymorphism #-}

module Issue229 where

open import Level

data Works a b : Set (suc a ⊔ suc b) where
  w : (A : Set a)(B : Set b) → Works a b

record Doesn'tWork a b : Set (suc a ⊔ suc b) where
  field
    A : Set a
    B : Set b

-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/Interaction/Highlighting/Generate.hs:469
