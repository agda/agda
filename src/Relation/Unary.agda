------------------------------------------------------------------------
-- The Agda standard library
--
-- Unary relations
------------------------------------------------------------------------

module Relation.Unary where

open import Data.Empty
open import Function
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Level
open import Relation.Nullary

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

  -- Set union.

  infixl 6 _∪_

  _∪_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Pred A _
  P ∪ Q = λ x → x ∈ P ⊎ x ∈ Q

  -- Set intersection.

  infixl 7 _∩_

  _∩_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Pred A _
  P ∩ Q = λ x → x ∈ P × x ∈ Q

------------------------------------------------------------------------
-- Unary relation combinators

infixr 2 _⟨×⟩_
infixr 1 _⟨⊎⟩_
infixr 0 _⟨→⟩_

_⟨×⟩_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
        Pred A ℓ₁ → Pred B ℓ₂ → Pred (A × B) _
P ⟨×⟩ Q = uncurry (λ p q → P p × Q q)

_⟨⊎⟩_ : ∀ {a b ℓ} {A : Set a} {B : Set b} →
        Pred A ℓ → Pred B ℓ → Pred (A ⊎ B) _
P ⟨⊎⟩ Q = [ P , Q ]

_⟨→⟩_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
        Pred A ℓ₁ → Pred B ℓ₂ → Pred (A → B) _
(P ⟨→⟩ Q) f = P ⊆ Q ∘ f

------------------------------------------------------------------------
-- Properties of unary relations

Decidable : ∀ {a p} {A : Set a} (P : A → Set p) → Set _
Decidable P = ∀ x → Dec (P x)
