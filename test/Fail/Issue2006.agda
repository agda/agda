
open import Agda.Primitive
open import Common.Reflection
open import Common.Prelude

macro
  deBruijn : Nat → Term → TC ⊤
  deBruijn n = unify (lam visible (abs "x" (var n [])))

data Vec {a} (A : Set a) : Nat → Set a where
  [] : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

module _ {n} {a} {A : Set a} (xs : Vec A n) where

  ok : Nat → Nat → Nat
  ok k = deBruijn 5

  -- Should give a nice error, not 'panic: variable @6 out of scope'.
  not-ok : Nat → Nat → Nat
  not-ok k = deBruijn 6
