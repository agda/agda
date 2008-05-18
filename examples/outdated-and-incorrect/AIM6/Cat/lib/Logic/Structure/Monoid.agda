
module Logic.Structure.Monoid where

import Logic.Equivalence
import Logic.Operations as Operations

open Logic.Equivalence using (Equivalence; module Equivalence)
open Operations.Param

data Monoid (A : Set)(Eq : Equivalence A) : Set where
  monoid :
    (z   : A)
    (_+_ : A -> A -> A)
    (leftId : LeftIdentity Eq z _+_)
    (rightId : RightIdentity Eq z _+_)
    (assoc : Associative Eq _+_) ->
    Monoid A Eq

-- There should be a simpler way of doing this. Local definitions to data declarations?

module Projections where

  zero : {A : Set}{Eq : Equivalence A} -> Monoid A Eq -> A
  zero (monoid z _ _ _ _) = z

  plus : {A : Set}{Eq : Equivalence A} -> Monoid A Eq -> A -> A -> A
  plus (monoid _ p _ _ _) = p

  leftId : {A : Set}{Eq : Equivalence A}(Mon : Monoid A Eq) -> LeftIdentity Eq (zero Mon) (plus Mon)
  leftId (monoid _ _ li _ _) = li

  rightId : {A : Set}{Eq : Equivalence A}(Mon : Monoid A Eq) -> RightIdentity Eq (zero Mon) (plus Mon)
  rightId (monoid _ _ _ ri _) = ri

  assoc : {A : Set}{Eq : Equivalence A}(Mon : Monoid A Eq) -> Associative Eq (plus Mon)
  assoc (monoid _ _ _ _ a) = a

module Monoid {A : Set}{Eq : Equivalence A}(Mon : Monoid A Eq) where

  zero    = Projections.zero Mon
  _+_     = Projections.plus Mon
  leftId  = Projections.leftId Mon
  rightId = Projections.rightId Mon
  assoc   = Projections.assoc Mon

