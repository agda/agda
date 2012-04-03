-- Andreas, 2012-01-12
module Common.Irrelevance where

open import Common.Level

postulate
  .irrAxiom : ∀ {a}{A : Set a} → .A → A
{-# BUILTIN IRRAXIOM irrAxiom #-}

record Squash {a}(A : Set a) : Set a where
  constructor squash
  field
    .unsquash : A
open Squash public
