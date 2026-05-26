{-# OPTIONS --smart-with #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

foo : (f : Nat → Nat) (x : Nat) → f x ≡ f (f x) → f x ≡ f x
foo f x p rewrite p = refl
