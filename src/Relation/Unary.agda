------------------------------------------------------------------------
-- The Agda standard library
--
-- Unary relations
------------------------------------------------------------------------

module Relation.Unary where

open import Data.Empty
open import Function
open import Data.Unit.Minimal using (⊤)
open import Data.Product
open import Data.Sum
open import Level
open import Relation.Nullary
open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Unary relations

Pred : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
Pred A ℓ = A → Set ℓ

------------------------------------------------------------------------
-- Unary relations can be seen as sets

-- I.e., they can be seen as subsets of the universe of discourse.

module _ {a} {A : Set a} -- The universe of discourse.
         where

  -- Set membership.

  infix 4 _∈_ _∉_

  _∈_ : ∀ {ℓ} → A → Pred A ℓ → Set _
  x ∈ P = P x

  _∉_ : ∀ {ℓ} → A → Pred A ℓ → Set _
  x ∉ P = ¬ x ∈ P

  -- The empty set.

  ∅ : Pred A zero
  ∅ = λ _ → ⊥

  -- The property of being empty.

  Empty : ∀ {ℓ} → Pred A ℓ → Set _
  Empty P = ∀ x → x ∉ P

  ∅-Empty : Empty ∅
  ∅-Empty x ()

  -- The singleton set.
  ｛_｝ : A → Pred A a
  ｛ x ｝ = _≡_ x

  -- The universe, i.e. the subset containing all elements in A.

  U : Pred A zero
  U = λ _ → ⊤

  -- The property of being universal.

  Universal : ∀ {ℓ} → Pred A ℓ → Set _
  Universal P = ∀ x → x ∈ P

  U-Universal : Universal U
  U-Universal = λ _ → _

  -- Set complement.

  ∁ : ∀ {ℓ} → Pred A ℓ → Pred A ℓ
  ∁ P = λ x → x ∉ P

  ∁∅-Universal : Universal (∁ ∅)
  ∁∅-Universal = λ x x∈∅ → x∈∅

  ∁U-Empty : Empty (∁ U)
  ∁U-Empty = λ x x∈∁U → x∈∁U _

  -- P ⊆ Q means that P is a subset of Q. _⊆′_ is a variant of _⊆_.

  infix 4 _⊆_ _⊇_ _⊆′_ _⊇′_

  _⊆_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
  P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

  _⊆′_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
  P ⊆′ Q = ∀ x → x ∈ P → x ∈ Q

  _⊇_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
  Q ⊇ P = P ⊆ Q

  _⊇′_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
  Q ⊇′ P = P ⊆′ Q

  ∅-⊆ : ∀ {ℓ} → (P : Pred A ℓ) → ∅ ⊆ P
  ∅-⊆ P ()

  ⊆-U : ∀ {ℓ} → (P : Pred A ℓ) → P ⊆ U
  ⊆-U P _ = _

  -- Positive version of non-disjointness, dual to inclusion.

  infix 4 _≬_

  _≬_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
  P ≬ Q = ∃ λ x → x ∈ P × x ∈ Q

  -- Set union.

  infixr 6 _∪_

  _∪_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Pred A _
  P ∪ Q = λ x → x ∈ P ⊎ x ∈ Q

  -- Set intersection.

  infixr 7 _∩_

  _∩_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Pred A _
  P ∩ Q = λ x → x ∈ P × x ∈ Q

  -- Implication.

  infixl 8 _⇒_

  _⇒_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Pred A _
  P ⇒ Q = λ x → x ∈ P → x ∈ Q

  -- Infinitary union and intersection.

  infix 9 ⋃ ⋂

  ⋃ : ∀ {ℓ i} (I : Set i) → (I → Pred A ℓ) → Pred A _
  ⋃ I P = λ x → Σ[ i ∈ I ] P i x

  syntax ⋃ I (λ i → P) = ⋃[ i ∶ I ] P

  ⋂ : ∀ {ℓ i} (I : Set i) → (I → Pred A ℓ) → Pred A _
  ⋂ I P = λ x → (i : I) → P i x

  syntax ⋂ I (λ i → P) = ⋂[ i ∶ I ] P

------------------------------------------------------------------------
-- Unary relation combinators

infixr 2 _⟨×⟩_
infixr 2 _⟨⊙⟩_
infixr 1 _⟨⊎⟩_
infixr 0 _⟨→⟩_
infixl 9 _⟨·⟩_
infixr 9 _⟨∘⟩_
infixr 2 _//_ _\\_

_⟨×⟩_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
        Pred A ℓ₁ → Pred B ℓ₂ → Pred (A × B) _
(P ⟨×⟩ Q) (x , y) = x ∈ P × y ∈ Q

_⟨⊙⟩_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
        Pred A ℓ₁ → Pred B ℓ₂ → Pred (A × B) _
(P ⟨⊙⟩ Q) (x , y) = x ∈ P ⊎ y ∈ Q

_⟨⊎⟩_ : ∀ {a b ℓ} {A : Set a} {B : Set b} →
        Pred A ℓ → Pred B ℓ → Pred (A ⊎ B) _
P ⟨⊎⟩ Q = [ P , Q ]

_⟨→⟩_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
        Pred A ℓ₁ → Pred B ℓ₂ → Pred (A → B) _
(P ⟨→⟩ Q) f = P ⊆ Q ∘ f

_⟨·⟩_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
        (P : Pred A ℓ₁) (Q : Pred B ℓ₂) →
        (P ⟨×⟩ (P ⟨→⟩ Q)) ⊆ Q ∘ uncurry (flip _$_)
(P ⟨·⟩ Q) (p , f) = f p

-- Converse.

_~ : ∀ {a b ℓ} {A : Set a} {B : Set b} →
     Pred (A × B) ℓ → Pred (B × A) ℓ
P ~ = P ∘ swap

-- Composition.

_⟨∘⟩_ : ∀ {a b c ℓ₁ ℓ₂} {A : Set a} {B : Set b} {C : Set c} →
        Pred (A × B) ℓ₁ → Pred (B × C) ℓ₂ → Pred (A × C) _
(P ⟨∘⟩ Q) (x , z) = ∃ λ y → (x , y) ∈ P × (y , z) ∈ Q

-- Post and pre-division.

_//_ : ∀ {a b c ℓ₁ ℓ₂} {A : Set a} {B : Set b} {C : Set c} →
       Pred (A × C) ℓ₁ → Pred (B × C) ℓ₂ → Pred (A × B) _
(P // Q) (x , y) = Q ∘ _,_ y ⊆ P ∘ _,_ x

_\\_ : ∀ {a b c ℓ₁ ℓ₂} {A : Set a} {B : Set b} {C : Set c} →
       Pred (A × C) ℓ₁ → Pred (A × B) ℓ₂ → Pred (B × C) _
P \\ Q = (P ~ // Q ~) ~

------------------------------------------------------------------------
-- Properties of unary relations

Decidable : ∀ {a ℓ} {A : Set a} (P : Pred A ℓ) → Set _
Decidable P = ∀ x → Dec (P x)
