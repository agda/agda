{-# OPTIONS --rewriting --guardedness #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality

tac : Term → TC ⊤
tac hole = unify hole (lit (nat 42))

record R {@(tactic tac) n : Nat} : Set where
  constructor c
  coinductive
  field
    π₁ : R
    π₂ : R {n}
    π₃ : R {42}
open R

test0  : R {0}
test42 : R

test0 .π₁ = test42
test0 .π₂ = test0
test0 .π₃ = test42

test42 .π₁ = test42
test42 .π₂ = test42
test42 .π₃ = test42
