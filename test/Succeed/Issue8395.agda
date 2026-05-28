-- Andreas, 2026-05-01, issue #8395
-- Crash in debug printing due to wrong context.

{-# OPTIONS -v tc.lhs.top:10 #-}

module Issue8395 where

postulate
  _≡_ : {A : Set} → A → A → Set
  List : Set → Set
  Any : {A : Set} (P : A → Set) → List A → Set

record Setoid : Set₁ where
  field
    Carrier : Set
    _≈_     : Carrier → Carrier → Set

setoid : Set → Setoid
setoid A = record
  { Carrier = A
  ; _≈_     = _≡_
  }

module Membership (S : Setoid) where
  open module S = Setoid S

  _∈_ : Carrier → List Carrier → Set _
  x ∈ xs = Any (_≈_ x) xs

-- Debug printing should succeed.
