module QuoteContext where

open import Common.Level
open import Common.Prelude
open import Common.Product
open import Common.Equality
open import Common.Reflection

Vec : Set → Nat → Set
Vec A zero = ⊤
Vec A (suc x) = A × Vec A x

test : (n : Nat) (v : Vec Nat n) (m : Nat) → List (Arg Type)
test zero v n = quoteContext
test (suc m) v n = quoteContext

test-zero : test 0 _ 0 ≡
  vArg (def (quote Nat) []) ∷
  vArg (def (quote Vec) (vArg (def (quote Nat) []) ∷
                         vArg (con (quote zero) []) ∷
                         [])) ∷
  []
test-zero = refl

test-suc : test 1 (zero , _) 0 ≡
  vArg (def (quote Nat) []) ∷
  vArg (def (quote Vec) (vArg (def (quote Nat) []) ∷
                         vArg (con (quote suc) (vArg (var 0 []) ∷ [])) ∷
                         [])) ∷
  vArg (def (quote Nat) []) ∷
  []
test-suc = refl
