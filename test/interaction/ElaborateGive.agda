module ElaborateGive where

open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

macro
  addUnknown : Term → TC ⊤
  addUnknown goal = unify goal
                          (def (quote _+_)
                            (arg (arg-info visible relevant) unknown ∷
                            arg (arg-info visible relevant) unknown ∷ []))

unknownPlus : Nat
unknownPlus = {!!}

five : Nat
five = {!!}
