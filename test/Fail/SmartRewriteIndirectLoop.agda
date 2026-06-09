{-# OPTIONS --smart-with #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

foo : (f : Nat → Nat → Nat) (x : Nat) → f x ≡ (λ y → f y y) → f x x ≡ 42
foo f x p rewrite p = refl
