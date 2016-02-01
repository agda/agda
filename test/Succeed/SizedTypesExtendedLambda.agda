-- Andreas, 2013-11-23
-- Make sure sized types work with extended lambda

{-# OPTIONS --copatterns --sized-types #-}

-- {-# OPTIONS -v tc.def:100 -v tc.size:100 -v tc.meta.assign:20 #-}
-- {-# OPTIONS -v tc.lhs:15 -v tc.size:15 -v term:20 #-}

module SizedTypesExtendedLambda where

open import Common.Size
open import Common.Maybe

mutual

  data Delay (A : Set) (i : Size) : Set where
    fail  : Delay A i
    now   : A → Delay A i
    later : ∞Delay A i → Delay A i

  record ∞Delay (A : Set) (i : Size) : Set where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → Delay A j

open ∞Delay

postulate
  A : Set
  something : ∀ {C : Set} → (Maybe A → C) → C

mutual
  -- To termination check, the hidden i has to be moved to the lhs.
  --   test = \ {i} -> something...
  -- becomes
  --   test {i} = something ... (∞test {i} a) ...
  test : {i : Size} → Delay A i
  test = something λ
           { nothing  -> fail
           ; (just a) -> later (∞test a)
           }

  -- Because of trailing bounded size quantification, this is already in the form:
  --   force (∞test {i} a) {j} = test {j}
  ∞test : {i : Size} (a : A) → ∞Delay A i
  force (∞test a) = test
