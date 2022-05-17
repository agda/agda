open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.Reflection

pattern vArg x = arg (arg-info visible (modality relevant quantity-ω)) x

macro
  macaroo : Term → TC ⊤
  macaroo hole = unify hole (con (quote suc) (vArg unknown ∷ []))

test : Nat
test = macaroo
