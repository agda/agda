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
  ( ("b" , arg (argInfo visible relevant) unknown) ∷ [])
  ( arg (argInfo visible relevant) (var 0)
  ∷ arg (argInfo visible relevant) (con (quote box)
        (arg (argInfo visible relevant) (dot unknown) ∷ []))
  ∷ [])
  (var 0 []) ∷ [])

works₃ : (b : Bool) → Box b → (x y : Bool) → Bool
unquoteDef works₃ = defineFun works₃ (clause
  ( ("y" , arg (argInfo visible relevant) unknown)
  ∷ ("x" , arg (argInfo visible relevant) unknown)
  ∷ ("b" , arg (argInfo visible relevant) unknown)
  ∷ [])
  ( arg (argInfo visible relevant) (var 2)
  ∷ arg (argInfo visible relevant) (con (quote box)
        (arg (argInfo visible relevant) (dot unknown) ∷ []))
  ∷ arg (argInfo visible relevant) (var 1)
  ∷ arg (argInfo visible relevant) (var 0)
  ∷ [])
  (var 2 []) ∷ [])
