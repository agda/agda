open import Agda.Builtin.Reflection
open import Agda.Builtin.Sigma
open import Common.Equality
open import Common.List
open import Common.Reflection
open import Common.Unit

module ReflectionGetType where

macro
  byTC : ∀ {a} {A : Set a} → TC A → Term → TC Unit
  byTC comp goal = comp >>= quoteTC >>= unify goal

module Temp {A : Set} where

  id : A → A
  id a = a

  id-type₁ : Term
  id-type₁ = byTC (getType (quote id))

  -- inContext [] goes to the original context of the macro call, so
  -- it should not have any effect here.
  id-type₁' : Term
  id-type₁' = byTC (inContext [] (getType (quote id)))

  id-def₁ : Definition
  id-def₁ = byTC (getDefinition (quote id))

  -- same as above
  id-def₁' : Definition
  id-def₁' = byTC (inContext [] (getDefinition (quote id)))

open Temp

wrap : Term → Term
wrap t =
  pi (arg (arg-info hidden (modality relevant quantity-ω)) (agda-sort (lit 0)))
     (abs "A" t)

id-type₂ : Term
id-type₂ = byTC (getType (quote id))

id-def₂ : Definition
id-def₂ = byTC (getDefinition (quote id))

pf-type : ∀ {A} → wrap (id-type₁ {A}) ≡ id-type₂
pf-type = refl

pf-type' : ∀ {A} → id-type₁' {A} ≡ id-type₁ {A}
pf-type' = refl

pf-def : ∀ {A} →
  id-def₁ {A} ≡ function (clause (("a" , vArg (var 0 [])) ∷ []) (vArg (var 0) ∷ []) (var 0 []) ∷ [])
pf-def = refl

pf-def' : ∀ {A} → id-def₁' {A} ≡ id-def₁ {A}
pf-def' = refl
