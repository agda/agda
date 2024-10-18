{-# OPTIONS --polarity #-}

module _ where

open import Agda.Builtin.Nat

-- The following type-checks because the polarity system is pure and not
-- positional.
module M (@++ A : Set) where
  @- B : Set
  B = Nat

  @++ C : Set
  C = B
