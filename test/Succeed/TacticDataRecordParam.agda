{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality

tac : Term → TC ⊤
tac hole = unify hole (lit (nat 42))

module _ {@(tactic tac) n : Nat} where
  data D1 : Nat → Set where
    c1 : (m : Nat) → n ≡ m → D1 m

test : {m : Nat} → D1 m → m ≡ 42
test (c1 m refl) = refl

record R2 {@(tactic tac) n : Nat} : Set where
  constructor c2

test2 : R2 {42}
test2 = c2

data D3 {n : Nat} : Set

data D3 {@(tactic tac) n} where
  c3 : D3

test3 : D3
test3 = c3 {10}
