-- Andreas, 2024-01-02, issue #7044, test case by Christian Sattler.
-- This module has a blocked definition, which needs to be serialized
-- correctly as postulate blocked forever.

{-# OPTIONS --allow-unsolved-metas #-}

module Issue7044Import where

data T : Set where
  t : T

postulate
  X : Set
  x : X

A : Set
A = {!!}

foo : A → X
foo t = x
