
open import Agda.Builtin.List
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

postulate
  A B : Set
  @0 a : A

tac : Term → TC ⊤
tac = unify (def (quote a) [])

postulate
  f : {@0 @(tactic tac) x : A} → B

test : B
test = f
