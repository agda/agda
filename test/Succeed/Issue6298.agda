{-# OPTIONS --cubical-compatible --erasure #-}

module Issue6298 where

open import Agda.Builtin.Equality

-- The argument x looks like it might throw a spanner in the works, but
-- the trX-con clause generated here will be modality-correct
-- regardless. This is because the left inverse generated (really, the
-- unification log) will eliminate x in favour of y, instead of the
-- other way around.
J : ∀ (A : Set) (@0 x : A) (P : (y : A) → x ≡ y → Set) → (prefl : P x refl) → (y : A) (eq : x ≡ y) → P y eq
J A xyz P prefl x refl = prefl
