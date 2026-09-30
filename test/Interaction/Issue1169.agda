
-- The previous error was:
-- Auto in hole `?0` raises a typing error:
--   (zero ∷ L) != L of type (List ℕ)
--   when checking that the expression x₁ has type (foo L)

open import Agda.Builtin.List
open import Agda.Builtin.Nat

data ⊥ : Set where

foo : List Nat → Set
foo []          = ⊥
foo (zero ∷ L)  = foo L
foo (suc N ∷ L) = foo (suc N ∷ L)

bar : (L : List Nat) → (foo L) → List Nat
bar [] x = []
bar (zero ∷ L) x₁ = bar L {!!}
bar (suc x ∷ L) x₁ = {!!}
