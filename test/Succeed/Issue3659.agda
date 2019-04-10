{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Agda.Primitive.Cubical

module _ where

postulate
  PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ
{-# BUILTIN PATHP PathP #-}

data D {ℓ} (A : Set ℓ) : Set ℓ where
  c : PathP _ _ _
