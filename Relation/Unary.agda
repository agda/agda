------------------------------------------------------------------------
-- Unary relations
------------------------------------------------------------------------

module Relation.Unary where

------------------------------------------------------------------------
-- Unary relations

Pred : Set -> Set1
Pred a = a -> Set

-- Unary relations can be seen as sets.

_∈_ : {a : Set} -> a -> Pred a -> Set
x ∈ P = P x

------------------------------------------------------------------------
-- Simple properties of unary relations

infixr 4 _⟶_

_⟶_ : forall {a} -> Pred a -> Pred a -> Set
P ⟶ Q = forall x -> P x -> Q x
