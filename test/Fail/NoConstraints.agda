open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

P : Bool → Set
P true  = Bool
P false = Bool

f : (b : Bool) → P b
f true  = true
f false = false

pattern varg x = arg (arg-info visible relevant) x

create-constraint : TC Set
create-constraint =
  unquoteTC (def (quote P)
               (varg (def (quote f) (varg unknown ∷ [])) ∷ []))

macro

  should-fail : Term → TC ⊤
  should-fail _ =
    bindTC (noConstraints create-constraint) λ _ →
    returnTC tt

test : ⊤
test = should-fail
