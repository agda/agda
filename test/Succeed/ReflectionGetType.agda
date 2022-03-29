open import Agda.Builtin.Reflection
open import Common.Equality
open import Common.Reflection
open import Common.Unit
open import Common.List

module ReflectionGetType where

macro
  byTC : ∀ {a} {A : Set a} → TC A → Term → TC Unit
  byTC comp goal = comp >>= quoteTC >>= unify goal

module Temp {A : Set} where

  id : A → A
  id a = a

  id-type₁ : Term
  id-type₁ = byTC (getType (quote id))

open Temp

wrap : Term → Term
wrap t =
  pi (arg (arg-info hidden (modality relevant quantity-ω)) (agda-sort (lit 0)))
     (abs "A" t)

id-type₂ : Term
id-type₂ = byTC (getType (quote id))

pf : ∀ {A} → wrap (id-type₁ {A}) ≡ id-type₂
pf = refl
