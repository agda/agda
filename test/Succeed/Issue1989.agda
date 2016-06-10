
module _ where

open import Agda.Builtin.Unit
open import Agda.Builtin.Reflection

data D (B : Set) {{b : B}} : Set where
  c : D B

postulate
  B : Set
  instance b : B
  T : D B → Set

macro
  this : Term → Term → TC ⊤
  this thing hole = unify hole thing

test₁ : _
test₁ = c {_} {{b}}

test₂ : D B
test₂ = c {_} {{b}}

test₃ : D B
test₃ = this (c {{b}})
