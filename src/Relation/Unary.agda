------------------------------------------------------------------------
-- Unary relations
------------------------------------------------------------------------

module Relation.Unary where

open import Data.Empty
open import Data.Function
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Relation.Nullary

------------------------------------------------------------------------
-- Unary relations

Pred : Set → Set₁
Pred a = a → Set

------------------------------------------------------------------------
-- Unary relations can be seen as sets

-- I.e., they can be seen as subsets of the universe of discourse.

private
 module Dummy {a : Set} -- The universe of discourse.
          where

  -- Set membership.

  infix 4 _∈_ _∉_

  _∈_ : a → Pred a → Set
  x ∈ P = P x

  _∉_ : a → Pred a → Set
  x ∉ P = ¬ x ∈ P

  -- The empty set.

  ∅ : Pred a
  ∅ = λ _ → ⊥

  -- The property of being empty.

  Empty : Pred a → Set
  Empty P = ∀ x → x ∉ P

  ∅-Empty : Empty ∅
  ∅-Empty x ()

  -- The universe, i.e. the subset containing all elements in a.

  U : Pred a
  U = λ _ → ⊤

  -- The property of being universal.

  Universal : Pred a → Set
  Universal P = ∀ x → x ∈ P

  U-Universal : Universal U
  U-Universal = λ _ → _

  -- Set complement.

  ∁ : Pred a → Pred a
  ∁ P = λ x → x ∉ P

  ∁∅-Universal : Universal (∁ ∅)
  ∁∅-Universal = λ x x∈∅ → x∈∅

  ∁U-Empty : Empty (∁ U)
  ∁U-Empty = λ x x∈∁U → x∈∁U _

  -- P ⊆ Q means that P is a subset of Q. _⊆′_ is a variant of _⊆_.

  infix 4 _⊆_ _⊇_ _⊆′_ _⊇′_

  _⊆_ : Pred a → Pred a → Set
  P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

  _⊆′_ : Pred a → Pred a → Set
  P ⊆′ Q = ∀ x → x ∈ P → x ∈ Q

  _⊇_ : Pred a → Pred a → Set
  Q ⊇ P = P ⊆ Q

  _⊇′_ : Pred a → Pred a → Set
  Q ⊇′ P = P ⊆′ Q

  ∅-⊆ : (P : Pred a) → ∅ ⊆ P
  ∅-⊆ P ()

  ⊆-U : (P : Pred a) → P ⊆ U
  ⊆-U P _ = _

  -- Set union.

  infixl 6 _∪_

  _∪_ : Pred a → Pred a → Pred a
  P ∪ Q = λ x → x ∈ P ⊎ x ∈ Q

  -- Set intersection.

  infixl 7 _∩_

  _∩_ : Pred a → Pred a → Pred a
  P ∩ Q = λ x → x ∈ P × x ∈ Q

open Dummy public

------------------------------------------------------------------------
-- Unary relation combinators

infixr 2 _⟨×⟩_
infixr 1 _⟨⊎⟩_
infixr 0 _⟨→⟩_

_⟨×⟩_ : ∀ {A B} → Pred A → Pred B → Pred (A × B)
(P ⟨×⟩ Q) p = P (proj₁ p) × Q (proj₂ p)

_⟨⊎⟩_ : ∀ {A B} → Pred A → Pred B → Pred (A ⊎ B)
(P ⟨⊎⟩ Q) (inj₁ p) = P p
(P ⟨⊎⟩ Q) (inj₂ q) = Q q

_⟨→⟩_ : ∀ {A B} → Pred A → Pred B → Pred (A → B)
(P ⟨→⟩ Q) f = P ⊆ Q ∘₀ f
