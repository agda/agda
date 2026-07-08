{-# OPTIONS --smart-with #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

data ⊥ : Set where

data Foo : Set
record Bar : Set

data Foo where
  b : Bar → Foo

record Bar where
  inductive
  field
    app : Nat → Foo
open Bar

rec : Foo → ⊥
rec (b f) = rec (f .app 0)

bad : (x : Bar) → x .app 0 ≡ b x → Nat
bad x p rewrite p = {!!}
