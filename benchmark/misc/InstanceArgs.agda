module InstanceArgs where

data UnitMonoid : Set where
  u : UnitMonoid
  p : UnitMonoid → UnitMonoid → UnitMonoid

record Plus (A : Set) : Set where
  infixl 6 _+_
  field
    _+_ : A → A → A

open Plus {{...}}

instance
  plus-unitMonoid : Plus UnitMonoid
  plus-unitMonoid = record { _+_ = p }

bigValue : UnitMonoid
bigValue =
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u +
  u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u + u
