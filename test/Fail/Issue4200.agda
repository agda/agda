-- Andreas, 2019-12-03, issue #4200 reported and testcase by nad

{-# OPTIONS --erasure #-}

open import Agda.Builtin.Bool

data D : Set where
  c₁ : D
  @0 c₂ : D

f : D → Bool
f c₁ = true
f c₂ = false

@0 _ : D
_ = c₂  -- OK.

_ : D
_ = c₂  -- Not allowed.

-- Expected error:

-- Identifier c₂ is declared erased, so it cannot be used here
-- when checking that the expression c₂ has type D
