------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of sums (disjoint unions)
------------------------------------------------------------------------

module Data.Sum.Properties where

open import Data.Sum
open import Function
open import Relation.Binary.PropositionalEquality

module _ {a b} {A : Set a} {B : Set b} where

 inj₁-injective : ∀ {x y} → (A ⊎ B ∋ inj₁ x) ≡ inj₁ y → x ≡ y
 inj₁-injective refl = refl

 inj₂-injective : ∀ {x y} → (A ⊎ B ∋ inj₂ x) ≡ inj₂ y → x ≡ y
 inj₂-injective refl = refl
