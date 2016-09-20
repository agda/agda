-- Andreas, 2016-09-20 test whether --no-eta-equality is respected

{-# OPTIONS --no-eta-equality #-}

open import Common.Equality

data Wrap (A : Set) : Set where
  wrap : A → Wrap A

record R : Set where
  inductive
  constructor c
  field p : Wrap R
open R

test : ∀ (w : R) → w ≡ c (p w)
test w = refl  -- should fail
