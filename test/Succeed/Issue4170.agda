open import Agda.Builtin.Reflection
open import Agda.Builtin.List
open import Agda.Builtin.Unit

data World : Set where
  ww : World

test : Term → TC ⊤
test hole
  = unify (con (quote ww) []) hole

HVet : Set₁
HVet = {@(tactic test) w : World} → Set

a : {HQ : HVet} → HQ → ⊤
a = _
