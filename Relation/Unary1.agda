------------------------------------------------------------------------
-- Unary relations (variant for Set1)
------------------------------------------------------------------------

-- I want universe polymorphism.

module Relation.Unary1 where

------------------------------------------------------------------------
-- Unary relations

Pred : Set → Set2
Pred a = a → Set1

------------------------------------------------------------------------
-- Unary relations can be seen as sets

-- I.e., they can be seen as subsets of the universe of discourse.

private
 module Dummy {a : Set} -- The universe of discourse.
          where

  -- Set membership.

  infix 4 _∈_

  _∈_ : a → Pred a → Set1
  x ∈ P = P x

  -- The property of being universal.

  Universal : Pred a → Set1
  Universal P = ∀ x → x ∈ P

  -- P ⊆ Q means that P is a subset of Q.

  infix 4 _⊆_ _⊇_

  _⊆_ : Pred a → Pred a → Set1
  P ⊆ Q = ∀ x → x ∈ P → x ∈ Q

  _⊇_ : Pred a → Pred a → Set1
  Q ⊇ P = P ⊆ Q

open Dummy public
