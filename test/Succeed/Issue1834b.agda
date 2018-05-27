-- Andreas & James, 2016-04-18 pre-AIM XXIII
-- order of clauses should not matter here!

{-# OPTIONS --exact-split #-}

open import Common.Equality
open import Common.Prelude
open import Common.Product

thing : Bool → Bool × Bool
proj₁ (thing true) = false
proj₁ (thing false) = true
proj₂ (thing b) = b

test : ∀ b → proj₂ (thing b) ≡ b
test b = refl
