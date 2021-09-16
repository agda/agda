{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path

module _ where

data D {ℓ} (A : Set ℓ) : Set ℓ where
  c : PathP _ _ _
