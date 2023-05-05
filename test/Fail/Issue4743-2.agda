-- Macros that are run in type signatures of erased definitions can
-- only create erased definitions.

{-# OPTIONS --erasure #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

macro

  Unify-with-new-postulate : Term → TC ⊤
  Unify-with-new-postulate goal =
    bindTC (freshName "A") λ name →
    bindTC (declarePostulate
              (arg (arg-info visible (modality relevant quantity-ω))
                   name)
              (agda-sort (lit 0))) λ _ →
    unify goal (def name [])

mutual

  B : Set
  B = _

  @0 B≡ : B ≡ Unify-with-new-postulate
  B≡ = refl
