{-# OPTIONS -v tc.unquote.clause:30 #-}

open import Common.Reflection
open import Common.Prelude
open import Agda.Builtin.Sigma

data Box : Set → Set₁ where
  box : (A : Set) → Box A

unquoteDecl test = define (vArg test) (funDef
 (pi
   (vArg (sort (lit 0)))
   (abs "A" (pi
    (vArg (def (quote Box) (vArg (var 0 []) ∷ [])))
    (abs "x" (sort (lit 0))))))
 (clause
   (("dot" , vArg unknown) ∷ [])
   (vArg (dot unknown) ∷
    vArg (con (quote box) (vArg (var 0) ∷ [])) ∷ [])
   (var 1 [])
 ∷ []))
