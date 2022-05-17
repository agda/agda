open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Reflection

id : {A : Set} → A → A
id x = x

macro
  tac : Term → TC ⊤
  tac hole =
    unify hole
      (def (quote id)
         (arg (arg-info visible (modality relevant quantity-ω))
              (var 0 []) ∷
          []))

test : {A : Set} → A → A
test x = {!tac!}
