{-# OPTIONS --universe-polymorphism #-}

-- Should give some unsolved metas
module Issue203b where

open import Imports.Level

-- Should work but give unsolved metas (type of b)
data ↓ {a b} (A : Set a) : Set a where
  [_] : (x : A) → ↓ A

-- Shouldn't instantiate the level of Σ to a
data Σ {a b} (A : Set a) (B : A → Set b) : Set _ where
  _,_ : (x : A) (y : B x) → Σ A B
