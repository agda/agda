{-# OPTIONS --erasure #-}

open import Agda.Primitive
open import Agda.Builtin.List
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma

id : (@0 A : Set) → A → A
id _ x = x

macro
  @0 Unit : Term → TC ⊤
  Unit goal =
    bindTC (inferType (def (quote id) [])) λ t →
    bindTC (workOnTypes (reduce t)) λ _ →
    unify goal (def (quote ⊤) [])

_ : Set
_ = Unit

macro
  testM : Term → TC ⊤
  testM hole = bindTC (getType (quote _,_)) (λ t → workOnTypes (unify hole t))

test : Setω
test = testM
