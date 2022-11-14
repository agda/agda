{-# OPTIONS --cubical --safe --two-level #-}

module Issue6015 where

open import Agda.Primitive
open import Agda.Primitive.Cubical

data Idₛ {ℓ} (A : SSet ℓ) (a : A) : A → SSet ℓ where
  reflₛ : Idₛ A a a

module _ (i : I) where
  _ : Idₛ (SSet _) (Partial i1 (Set lzero)) (.(IsOne i1) → (Set lzero))
  _ = reflₛ

-- Should fail with "one is a type of partial elements, one is a
-- function type", since Partial and erased-IsOne-pis behave differently
-- when used as the domain of comparison for terms
