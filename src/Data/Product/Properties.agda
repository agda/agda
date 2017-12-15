------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of products
------------------------------------------------------------------------

module Data.Product.Properties where

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

module _ {a b} {A : Set a} {B : A → Set b} where

 ,-injectiveˡ : ∀ {a c} {b : B a} {d : B c} → (a , b) ≡ (c , d) → a ≡ c
 ,-injectiveˡ refl = refl

 ,-injectiveʳ : ∀ {a} {b c : B a} → (Σ A B ∋ (a , b)) ≡ (a , c) → b ≡ c
 ,-injectiveʳ refl = refl

