-- Liang-Ting, 2022-01-14, issue #5734

{-# OPTIONS --cubical-compatible #-}

open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Sigma
open import Agda.Builtin.Reflection
  renaming (returnTC to return; bindTC to _>>=_)
open import Agda.Primitive

private variable
  A B : Set _

reverseApp : List A → List A → List A
reverseApp []       ys = ys
reverseApp (x ∷ xs) ys = reverseApp xs (x ∷ ys)

reverse : List A → List A
reverse xs = reverseApp xs []

extend*Context : Telescope → TC A → TC A
extend*Context []              m = m
extend*Context ((s , a) ∷ tel) m = extendContext s a (extend*Context tel m)

pattern vArg x = arg (arg-info visible (modality relevant quantity-ω)) x
pattern visible-relevant-erased = arg-info visible (modality relevant quantity-0)
pattern var₀ x = var x []

Γ : Telescope
Γ =   ("ℓ" , arg visible-relevant-erased (quoteTerm Level))
    ∷ ("A" , vArg (agda-sort (set (var₀ 0))))
    ∷ []

macro
  m : Term → TC ⊤
  m hole = do
    _ ← extend*Context Γ do
      _ ← checkType (var₀ 0) (agda-sort (set (var₀ 1)))
      return tt
    inContext (reverse Γ) do
      return tt

_ : ⊤
_ = m
