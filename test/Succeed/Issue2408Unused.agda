-- Andreas, 2017-01-18, issue #2408

-- DLubs were not serialized, thus, there was a problem with
-- level dependent on unused values.

{-# OPTIONS --show-irrelevant #-}

-- {-# OPTIONS -v tc:20 #-}

open import Agda.Primitive

data ⊥ : Set where

data Unit : Set where
  unit : Unit

-- Argument a is unused in l
l : (u : Unit) (a : ⊥) → Level
l unit a = lzero

postulate
  u : Unit
  F : (a : ⊥) → Set (l u a)

-- checked type signature
--   F : (a : ⊥) → Set (l u a)
--   of sort  dLub Set (λ a → Set (lsuc (l u a)))
