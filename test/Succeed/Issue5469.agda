open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.Reflection

pattern vArg x = arg (arg-info visible (modality relevant quantity-ω)) x

make2 : Term → TC ⊤
make2 hole = bindTC (normalise (def (quote _+_) (vArg (lit (nat 1)) ∷ vArg (lit (nat 1)) ∷ []))) (unify hole)

macro
  tester : Term → TC ⊤
  tester hole = withReduceDefs (true , (quote _+_ ∷ [])) (make2 hole)

_ = tester
