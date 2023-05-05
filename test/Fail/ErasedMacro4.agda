{-# OPTIONS --erasure #-}

open import Agda.Builtin.List
open import Agda.Builtin.Reflection
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

@0 m : Name → TC ⊤
m F = defineFun F
  (clause
     (( "A"
      , arg (arg-info visible (modality relevant quantity-0))
          (agda-sort (lit 0))) ∷
      [])
     (arg (arg-info visible (modality relevant quantity-0)) (var 0) ∷
      [])
     (var 0 []) ∷
   [])

F : @0 Set → Set
unquoteDef F = m F
