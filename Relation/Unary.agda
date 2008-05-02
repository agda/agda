------------------------------------------------------------------------
-- Unary relations
------------------------------------------------------------------------

module Relation.Unary where

open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Relation.Nullary

------------------------------------------------------------------------
-- Unary relations

Pred : Set -> Set1
Pred a = a -> Set

------------------------------------------------------------------------
-- Unary relations can be seen as sets

-- I.e., they can be seen as subsets of the universe of discourse.

private
 module Dummy {a : Set} -- The universe of discourse.
          where

  -- Set membership.

  infix 4 _∈_ _∉_

  _∈_ : a -> Pred a -> Set
  x ∈ P = P x

  _∉_ : a -> Pred a -> Set
  x ∉ P = ¬ x ∈ P

  -- The empty set.

  ∅ : Pred a
  ∅ = \_ -> ⊥

  -- The property of being empty.

  Empty : Pred a -> Set
  Empty P = forall x -> x ∉ P

  ∅-Empty : Empty ∅
  ∅-Empty x ()

  -- The universe, i.e. the subset containing all elements in a.

  U : Pred a
  U = \_ -> ⊤

  -- The property of being universal.

  Universal : Pred a -> Set
  Universal P = forall x -> x ∈ P

  U-Universal : Universal U
  U-Universal = \_ -> _

  -- Set complement.

  ∁ : Pred a -> Pred a
  ∁ P = \x -> x ∉ P

  ∁∅-Universal : Universal (∁ ∅)
  ∁∅-Universal = \x x∈∅ -> x∈∅

  ∁U-Empty : Empty (∁ U)
  ∁U-Empty = \x x∈∁U -> x∈∁U _

  -- P ⊆ Q means that P is a subset of Q.

  infix 4 _⊆_

  _⊆_ : Pred a -> Pred a -> Set
  P ⊆ Q = forall x -> x ∈ P -> x ∈ Q

  ∅-⊆ : (P : Pred a) -> ∅ ⊆ P
  ∅-⊆ P x ()

  ⊆-U : (P : Pred a) -> P ⊆ U
  ⊆-U P x _ = _

  -- Set union.

  infixl 6 _∪_

  _∪_ : Pred a -> Pred a -> Pred a
  P ∪ Q = \x -> x ∈ P ⊎ x ∈ Q

  -- Set intersection.

  infixl 7 _∩_

  _∩_ : Pred a -> Pred a -> Pred a
  P ∩ Q = \x -> x ∈ P × x ∈ Q

open Dummy public
