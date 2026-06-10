{-# OPTIONS --smart-with #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

record Weird : Set where
  no-eta-equality
  constructor mk
  field
    app : Nat → Nat
open Weird

wah : (f : Nat → Weird) → Weird
wah f .app x = f x .app x

foo : (f : Nat → Weird) (x : Nat) → f x ≡ wah f → f x .app x ≡ 42
foo f x p rewrite p = refl
