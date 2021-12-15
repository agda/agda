open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.Reflection

macro
  printType : Term → TC ⊤
  printType hole = bindTC (inferType hole) λ t → typeError (termErr t ∷ [])

test1 : (a : Nat) → Nat
test1 = {! printType  !}

test2 : (a : Bool) → Bool
test2 = {! printType  !}
