------------------------------------------------------------------------
-- The Agda standard library
--
-- Predicate transformers
------------------------------------------------------------------------

module Relation.Unary.PredicateTransformer where

open import Level hiding (_⊔_)
open import Function
open import Data.Product
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary using (REL)

------------------------------------------------------------------------

-- Heterogeneous and homogeneous predicate transformers

PT : ∀ {a b} → Set a → Set b → (ℓ₁ ℓ₂ : Level) → Set _
PT A B ℓ₁ ℓ₂ = Pred A ℓ₁ → Pred B ℓ₂

Pt : ∀ {a} → Set a → (ℓ : Level) → Set _
Pt A ℓ = PT A A ℓ ℓ

-- Composition and identity

_⍮_ : ∀ {a b c ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : Set b} {C : Set c} →
      PT B C ℓ₂ ℓ₃ → PT A B ℓ₁ ℓ₂ → PT A C ℓ₁ _
S ⍮ T = S ∘ T

skip : ∀ {a ℓ} {A : Set a} → PT A A ℓ ℓ
skip P = P

------------------------------------------------------------------------
-- Operations on predicates extend pointwise to predicate transformers

module _ {a b} {A : Set a} {B : Set b} where

  -- The bottom and the top of the predicate transformer lattice.

  abort : PT A B zero zero
  abort = λ _ → ∅

  magic : PT A B zero zero
  magic = λ _ → U

  -- Negation.

  ∼_ : ∀ {ℓ₁ ℓ₂} → PT A B ℓ₁ ℓ₂ → PT A B ℓ₁ ℓ₂
  ∼ T = ∁ ∘ T

  -- Refinement.

  infix 4 _⊑_ _⊒_ _⊑′_ _⊒′_

  _⊑_ : ∀ {ℓ₁ ℓ₂} → PT A B ℓ₁ ℓ₂ → PT A B ℓ₁ ℓ₂ → Set _
  S ⊑ T = ∀ {X} → S X ⊆ T X

  _⊑′_ : ∀ {ℓ₁ ℓ₂} → PT A B ℓ₁ ℓ₂ → PT A B ℓ₁ ℓ₂ → Set _
  S ⊑′ T = ∀ X → S X ⊆ T X

  _⊒_ : ∀ {ℓ₁ ℓ₂} → PT A B ℓ₁ ℓ₂ → PT A B ℓ₁ ℓ₂ → Set _
  T ⊒ S = T ⊑ S

  _⊒′_ : ∀ {ℓ₁ ℓ₂} → PT A B ℓ₁ ℓ₂ → PT A B ℓ₁ ℓ₂ → Set _
  T ⊒′ S = S ⊑′ T

  -- The dual of refinement.

  infix 4 _⋢_

  _⋢_ : ∀ {ℓ₁ ℓ₂} → PT A B ℓ₁ ℓ₂ → PT A B ℓ₁ ℓ₂ → Set _
  S ⋢ T = ∃ λ X → S X ≬ T X

  -- Union.

  infixl 6 _⊓_

  _⊓_ : ∀ {ℓ₁ ℓ₂} → PT A B ℓ₁ ℓ₂ → PT A B ℓ₁ ℓ₂ → PT A B ℓ₁ ℓ₂
  S ⊓ T = λ X → S X ∪ T X

  -- Intersection.

  infixl 7 _⊔_

  _⊔_ : ∀ {ℓ₁ ℓ₂} → PT A B ℓ₁ ℓ₂ → PT A B ℓ₁ ℓ₂ → PT A B ℓ₁ ℓ₂
  S ⊔ T = λ X → S X ∩ T X

  -- Implication.

  infixl 8 _⇛_

  _⇛_ : ∀ {ℓ₁ ℓ₂} → PT A B ℓ₁ ℓ₂ → PT A B ℓ₁ ℓ₂ → PT A B ℓ₁ ℓ₂
  S ⇛ T = λ X → S X ⇒ T X

  -- Infinitary union and intersection.

  infix 9 ⨆ ⨅

  ⨆ : ∀ {ℓ₁ ℓ₂ i} (I : Set i) → (I → PT A B ℓ₁ ℓ₂) → PT A B ℓ₁ _
  ⨆ I T = λ X → ⋃[ i ∶ I ] T i X

  syntax ⨆ I (λ i → T) = ⨆[ i ∶ I ] T

  ⨅ : ∀ {ℓ₁ ℓ₂ i} (I : Set i) → (I → PT A B ℓ₁ ℓ₂) → PT A B ℓ₁ _
  ⨅ I T = λ X → ⋂[ i ∶ I ] T i X

  syntax ⨅ I (λ i → T) = ⨅[ i ∶ I ] T

  -- Angelic and demonic update.

  ⟨_⟩ : ∀ {ℓ} → REL A B ℓ → PT B A ℓ _
  ⟨ R ⟩ P = λ x → R x ≬ P

  [_] : ∀ {ℓ} → REL A B ℓ → PT B A ℓ _
  [ R ] P = λ x → R x ⊆ P
