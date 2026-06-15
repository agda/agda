{-# OPTIONS --smart-with #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

record Foo : Set where
  no-eta-equality
  field
    foo : Nat → Nat
    bar : Nat
open Foo

test : (x : Foo) → x .foo 0 ≡ 42 → x .bar ≡ 43 → Nat
test x p q
  rewrite p
  rewrite q
  = 44
