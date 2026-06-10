{-# OPTIONS --smart-with #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

data Unit : Set where
  ⟨⟩ : Unit

wah : (Nat → Unit → Nat → Nat) → Unit → Nat → Nat
wah f ⟨⟩ y = f y ⟨⟩ y

foo : (f : Nat → Unit → Nat → Nat) (x : Nat) → f x ≡ wah f → f x ⟨⟩ x ≡ 42
foo f x p rewrite p = refl
