{-# OPTIONS -v tc.unquote:30 #-}
open import Common.Prelude
open import Common.Reflection
open import Common.TC

data Box : Bool → Set where
  box : (b : Bool) → Box b

works : (b : Bool) → Box b → Bool
works b (box .b) = unquote (give (var 0 []))

works₂ : (b : Bool) → Box b → Bool
unquoteDef works₂ = defineFun works₂ (clause
  ( arg (argInfo visible relevant) (var "b")
  ∷ arg (argInfo visible relevant) (con (quote box)
        (arg (argInfo visible relevant) dot ∷ []))
  ∷ [])
  (var 0 []) ∷ [])

works₃ : (b : Bool) → Box b → (x y : Bool) → Bool
unquoteDef works₃ = defineFun works₃ (clause
  ( arg (argInfo visible relevant) (var "b")
  ∷ arg (argInfo visible relevant) (con (quote box)
        (arg (argInfo visible relevant) dot ∷ []))
  ∷ arg (argInfo visible relevant) (var "x")
  ∷ arg (argInfo visible relevant) (var "y")
  ∷ [])
  (var 2 []) ∷ [])
