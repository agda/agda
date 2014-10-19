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
  arg (argInfo visible relevant) (el (lit 0) (def (quote Nat) [])) ∷
  arg (argInfo visible relevant) (el (lit 0) (def (quote ⊤) [])) ∷ []
test-zero = refl

test-suc : test 1 (zero , _) 0 ≡
  arg (argInfo visible relevant) (el (lit 0) (def (quote Nat) [])) ∷
  arg (argInfo visible relevant) (el (lit 0)
    (def (quote Σ)
      (arg (argInfo hidden relevant) (def (quote lzero) []) ∷
       arg (argInfo hidden relevant) (def (quote lzero) []) ∷
       arg (argInfo visible relevant) (def (quote Nat) []) ∷
       arg (argInfo visible relevant) (lam visible (abs "x" (def (quote Vec)
         (arg (argInfo visible relevant) (def (quote Nat) []) ∷
          arg (argInfo visible relevant) (var 1 []) ∷ [])))) ∷ []))) ∷
  arg (argInfo visible relevant) (el (lit 0) (def (quote Nat) [])) ∷ []
test-suc = refl
