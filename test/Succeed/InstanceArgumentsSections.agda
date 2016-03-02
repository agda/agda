module InstanceArgumentsSections where

postulate  A : Set

module Basic where
  record B : Set where
    field bA : A

  open B {{...}}

  bA' : {{_ : B}} → A
  bA' = bA

module Parameterised (a : A) where
  record C : Set where
    field cA : A

  open C {{...}}

  cA' : {{_ : C}} → A
  cA' = cA

module RecordFromParameterised where
  postulate a : A

  open Parameterised a
  open C {{...}}

  cA'' : {{_ : C}} → A
  cA'' = cA

module RecordFromParameterisedInParameterised (a : A) where

  open Parameterised a
  open C {{...}}

  cA'' : {{_ : C}} → A
  cA'' = cA

module RecordFromParameterised' (a : A) where

  open Parameterised
  open C {{...}}

  cA'' : {{_ : C a}} → A
  cA'' = cA {a}

module AppliedRecord (a : A) where
  open Parameterised

  D : Set
  D = C a

  module D = C
  open D {{...}}

  dA' : {{_ : D}} → A
  dA' = cA {a}
