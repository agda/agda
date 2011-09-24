------------------------------------------------------------------------
-- The Agda standard library
--
-- W-types
------------------------------------------------------------------------

module Data.W where

open import Level
open import Relation.Nullary

-- The family of W-types.

data W {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  sup : (x : A) (f : B x → W A B) → W A B

-- Projections.

head : ∀ {a b} {A : Set a} {B : A → Set b} →
       W A B → A
head (sup x f) = x

tail : ∀ {a b} {A : Set a} {B : A → Set b} →
       (x : W A B) → B (head x) → W A B
tail (sup x f) = f

-- If B is always inhabited, then W A B is empty.

inhabited⇒empty : ∀ {a b} {A : Set a} {B : A → Set b} →
                  (∀ x → B x) → ¬ W A B
inhabited⇒empty b (sup x f) = inhabited⇒empty b (f (b x))
