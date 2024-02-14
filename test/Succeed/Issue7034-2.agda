-- Andreas, 2023-12-21, another test for #7034 by Christian Sattler

{-# OPTIONS --two-level --rewriting --confluence-check #-}

module Issue7034-2 where

open import Agda.Primitive using (SSet)

postulate
  X : SSet
  x : X
  Eq : X → X → SSet

{-# BUILTIN REWRITE Eq #-}

module _ (B : SSet) where
  record R : SSet where
    field
      b : B
      g : B → X

  postulate
    r : R
  open R r

  postulate
    rule : Eq (g b) x

{-# REWRITE rule #-}
