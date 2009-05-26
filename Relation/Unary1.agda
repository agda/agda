------------------------------------------------------------------------
-- Unary relations (variant for Set₁)
------------------------------------------------------------------------

-- I want universe polymorphism.

module Relation.Unary1 where

------------------------------------------------------------------------
-- Unary relations

Pred : Set → Set₂
Pred a = a → Set₁

------------------------------------------------------------------------
-- Unary relations can be seen as sets

-- I.e., they can be seen as subsets of the universe of discourse.

private
 module Dummy {a : Set} -- The universe of discourse.
          where

  -- Set membership.

  infix 4 _∈_

  _∈_ : a → Pred a → Set₁
  x ∈ P = P x

  -- The property of being universal.

  Universal : Pred a → Set₁
  Universal P = ∀ x → x ∈ P

  -- P ⊆ Q means that P is a subset of Q. _⊆′_ is a variant of _⊆_.

  infix 4 _⊆_ _⊇_ _⊆′_ _⊇′_

  _⊆_ : Pred a → Pred a → Set₁
  P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

  _⊆′_ : Pred a → Pred a → Set₁
  P ⊆′ Q = ∀ x → x ∈ P → x ∈ Q

  _⊇_ : Pred a → Pred a → Set₁
  Q ⊇ P = P ⊆ Q

  _⊇′_ : Pred a → Pred a → Set₁
  Q ⊇′ P = P ⊆′ Q

open Dummy public
