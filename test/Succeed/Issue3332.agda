-- Jesper, Andreas, 2018-10-29, issue #3332
--
-- WAS: With-inlining failed in termination checker
-- due to a DontCare protecting the clause bodies
-- (introduced by Prop).

{-# OPTIONS --prop #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.List

postulate
  A : Set

_++_ : List A → List A → List A
[] ++ l = l
(a ∷ l) ++ l' = a ∷ (l ++ l')

module PropEquality where

  data _≐_ {A : Set} (a : A) : A → Prop where
    refl : a ≐ a

  test : (l : List A) → (l ++ []) ≐ l
  test [] = refl
  test (x ∷ xs) with xs ++ [] | test xs
  test (x ∷ xs) | .xs | refl = refl

module SquashedEquality where

  data Squash (A : Set) : Prop where
    sq : A → Squash A

  test : (l : List A) → Squash (l ++ [] ≡ l)
  test [] = sq refl
  test (x ∷ l) with test l
  test (x ∷ l) | sq eq     with l ++ [] | eq
  test (x ∷ l) | .(test l) | .l | refl = sq refl

-- Both should succeed.
