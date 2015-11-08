-- Andreas, 2015-10-28 adapted from test case by
-- Ulf, 2014-02-06, shrunk from Wolfram Kahl's report

open import Common.Equality
open import Common.Unit
open import Common.Nat

postulate
  prop : ∀ x → x ≡ unit

record StrictTotalOrder : Set where
  field compare : Unit
open StrictTotalOrder

module M (Key : StrictTotalOrder) where

    postulate
      intersection′-₁ : ∀ x → x ≡ compare Key

    to-∈-intersection′  : Nat → Unit → Unit → Set
    to-∈-intersection′ zero x h = Unit
    to-∈-intersection′ (suc n) x h with intersection′-₁ x
    to-∈-intersection′ (suc n) ._ h  | refl with prop h
    to-∈-intersection′ (suc n) ._ ._ | refl    | refl = to-∈-intersection′ n unit unit
