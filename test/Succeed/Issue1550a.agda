-- Andreas, 2015-08-27 use imported rewrite rule

{-# OPTIONS --rewriting --confluence-check #-}

open import Common.Nat
open import Common.Equality

open import Issue1550

x+0+0+0 : ∀{x} → ((x + 0) + 0) + 0 ≡ x
x+0+0+0 = refl
