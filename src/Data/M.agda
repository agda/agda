------------------------------------------------------------------------
-- The Agda standard library
--
-- M-types (the dual of W-types)
------------------------------------------------------------------------

module Data.M where

open import Level
open import Coinduction

-- The family of M-types.

data M {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  inf : (x : A) (f : B x → ∞ (M A B)) → M A B

-- Projections.

head : ∀ {a b} {A : Set a} {B : A → Set b} →
       M A B → A
head (inf x f) = x

tail : ∀ {a b} {A : Set a} {B : A → Set b} →
       (x : M A B) → B (head x) → M A B
tail (inf x f) b = ♭ (f b)
