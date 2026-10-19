open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

tac : Term → TC ⊤
tac hole = unify hole (lit (nat 42))

data D {@(tactic tac) n : Nat} : Nat → Set where
  c : {m : Nat} → n ≡ m → D m
