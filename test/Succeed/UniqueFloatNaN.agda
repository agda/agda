module UniqueFloatNaN where

-- See Issue: Inconsistency: Rounding op differentiates NaNs #3749
-- https://github.com/agda/agda/issues/3749

open import Agda.Builtin.Float
  renaming ( primRound to round
           ; primFloor to floor
           ; primCeiling to ceiling
           ; primFloatNegate to -_
           ; primFloatDiv  to _/_)
open import Agda.Builtin.Equality

PNaN : Float
PNaN = 0.0 / 0.0

NNaN : Float
NNaN = - (0.0 / 0.0)

f : round PNaN ≡ round NNaN
f = refl

g : floor PNaN ≡ floor NNaN
g = refl

h : ceiling PNaN ≡ ceiling NNaN
h = refl
