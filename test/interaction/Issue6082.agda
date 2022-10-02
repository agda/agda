-- Andreas, 2022-09-29, issue #6082, test by Amelia.
-- Reflected syntax does not know about projections,
-- so when translating to abstract syntax, need to recover them.

{-# OPTIONS --postfix-projections #-}

open import Agda.Primitive
open import Agda.Builtin.Reflection
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Agda.Builtin.List

module _ {A : Set} {B : A → Set} (x : Σ A B) where
  ai : ArgInfo
  ai = arg-info visible (modality relevant quantity-ω)
  macro
    foo : Term → TC ⊤
    foo goal = unify goal (def (quote fst) (arg ai (var 0 []) ∷ []))

  _ : A
  _ = {! foo !}

-- M-x agda2-elaborate-give
-- should yield
-- x .fst
