{-# OPTIONS --erasure #-}
module UnquoteDataErased where

open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.Reflection
open import Common.Reflection
open import Common.List


defineD : Name → Name → Quantity → TC _
defineD n c q =
  declareData n 0 (quoteTerm Set) >>= λ _ →
  defineData n ((c , q
                   , pi (vArg (def (quote Nat) []))
                       (abs "" (def n []))) ∷ [])

unquoteDecl data newD0 constructor newC0 = defineD newD0 newC0 quantity-0

a : newD0
a = newC0 7
