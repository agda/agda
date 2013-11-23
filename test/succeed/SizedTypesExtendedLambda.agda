-- Andreas, 2013-11-23
-- Make sure sized types work with extended lambda

{-# OPTIONS --copatterns --sized-types #-}

-- {-# OPTIONS -v tc.def:100 -v tc.size:100 -v tc.meta.assign:20 #-}

module SizedTypesExtendedLambda where

open import Common.Size

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

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
  test : {i : Size} → Delay A i
  test = something λ
           { nothing  -> fail
           ; (just a) -> later (∞test a)
           }

  ∞test : {i : Size} (a : A) → ∞Delay A i
  force (∞test a) {j = _} = test
  -- force (∞test a) = test  -- still fails, unfortunately
