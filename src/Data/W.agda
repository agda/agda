------------------------------------------------------------------------
-- The Agda standard library
--
-- W-types
------------------------------------------------------------------------

module Data.W where

open import Level
open import Function
open import Relation.Unary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

-- The family of W-types.

data W {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  sup : (x : A) (f : B x → W A B) → W A B

module _ {a b} {A : Set a} {B : A → Set b} {x : A} {f : B x → W A B} where

 sup-injective₁ : ∀ {y g} → sup x f ≡ sup y g → x ≡ y
 sup-injective₁ refl = refl

 sup-injective₂ : ∀ {g} → sup x f ≡ sup x g → f ≡ g
 sup-injective₂ refl = refl

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
