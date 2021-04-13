{-# OPTIONS -v tc.unquote:30 #-}
open import Common.Prelude
open import Common.Reflection
open import Agda.Builtin.Sigma

data Box : Bool → Set where
  box : (b : Bool) → Box b

works : (b : Bool) → Box b → Bool
works b (box .b) = unquote (give (var 0 []))

works₂ : (b : Bool) → Box b → Bool
unquoteDef works₂ = defineFun works₂ (clause
  ( ("b" , vArg unknown) ∷ [])
  ( vArg (var 0)
  ∷ vArg (con (quote box)
        (vArg (dot unknown) ∷ []))
  ∷ [])
  (var 0 []) ∷ [])

works₃ : (b : Bool) → Box b → (x y : Bool) → Bool
unquoteDef works₃ = defineFun works₃ (clause
  ( ("y" , vArg unknown)
  ∷ ("x" , vArg unknown)
  ∷ ("b" , vArg unknown)
  ∷ [])
  ( vArg (var 2)
  ∷ vArg (con (quote box)
        (vArg (dot unknown) ∷ []))
  ∷ vArg (var 1)
  ∷ vArg (var 0)
  ∷ [])
  (var 2 []) ∷ [])
