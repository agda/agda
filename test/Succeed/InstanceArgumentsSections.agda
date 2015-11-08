module InstanceArgumentsSections where

postulate A : Set

module Basic where
  record B : Set where
    field bA : A

  open B {{...}}

  bA' : B → A
  bA' _ = bA

module Parameterised (a : A) where
  record C : Set where
    field cA : A

  open C {{...}}

  cA' : C → A
  cA' _ = cA

module RecordFromParameterised where
  postulate a : A

  open Parameterised a
  open C {{...}}

  cA'' : C → A
  cA'' _ = cA

module RecordFromParameterisedInParameterised (a : A) where

  open Parameterised a
  open C {{...}}

  cA'' : C → A
  cA'' _ = cA

module RecordFromParameterised' (a : A) where

  open Parameterised
  open C {{...}}

  cA'' : C a → A
  cA'' _ = cA a

module AppliedRecord (a : A) where
  open Parameterised

  D : Set
  D = C a

  module D = C a
  open D {{...}}

  dA' : D → A
  dA' _ = cA
