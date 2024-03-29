module _ where

open import Agda.Primitive.Cubical hiding (PathP)

postulate
  PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ

{-# BUILTIN PATHP        PathP     #-}
