{-# OPTIONS --cubical --safe --two-level #-}

module Issue6015 where

open import Agda.Primitive
open import Agda.Primitive.Cubical

data Idₛ {ℓ} (A : SSet ℓ) (a : A) : A → SSet ℓ where
  reflₛ : Idₛ A a a

module _ (i : I) where
  _ : Idₛ (SSet _) (Partial i1 (Set lzero)) (.(IsOne i1) → (Set lzero))
  _ = reflₛ

-- Should not display a hint: the normal form of Partial now reifies as Partial.
