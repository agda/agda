------------------------------------------------------------------------
-- The type Erased
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe --no-sized-types
            --no-guardedness --level-universe
            --erasure --erased-matches=none #-}

module Agda.Builtin.Erased.Erased where

open import Agda.Builtin.Equality
open import Agda.Primitive

private variable
  a : Level

-- The type Erased, which is a type-level variant of @0.
--
-- This type is defined as a record type *without* η-equality, in
-- anticipation of a possible future addition of linear types to Agda.
-- If η-equality is enabled, then the η-expansion of the linear
-- identity function λ x → x at type Erased A → Erased A is
-- λ x → [ erased x ], which is arguably not linear.

record Erased (@0 A : Set a) : Set a where
  no-eta-equality
  pattern
  constructor [_]
  field
    @0 erased : A

open Erased public
