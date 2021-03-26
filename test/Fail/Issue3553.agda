{-# OPTIONS --prop #-}

open import Agda.Builtin.Reflection
open import Agda.Builtin.List
open import Agda.Builtin.Unit
_>>=_ = bindTC
return = returnTC

postulate
  X : Prop
  x₀ : X

f : X
f = x₀

macro
  getValue : Name → Term → TC ⊤
  getValue s _ = do
    function (clause _ _ t ∷ []) ← getDefinition s
      where _ → typeError (strErr "Not a defined name" ∷ [])
    typeError (strErr "The value of " ∷ nameErr s ∷ strErr " is " ∷ termErr t ∷ [])

test = getValue f
