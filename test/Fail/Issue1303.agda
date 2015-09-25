{-# OPTIONS -v tc.unquote.clause:30 #-}

open import Common.Reflection
open import Common.Prelude

data Box : Set → Set₁ where
  box : (A : Set) → Box A

arg₀ : {A : Set} → A → Arg A
arg₀ = arg (argInfo visible relevant)


unquoteDecl test = funDef
 (el unknown (pi
   (arg₀ (el (lit 1) (sort (lit 0))))
   (abs "A" (el unknown (pi
    (arg₀ (el unknown (def (quote Box) (arg₀ (var 0 []) ∷ []))))
    (abs "x" (el (lit 1) (sort (lit 0)))))))))
 (clause
   (arg₀ dot ∷
    arg₀ (con (quote box) (arg₀ (var "dot") ∷ [])) ∷ [])
   (var 1 [])
 ∷ [])
