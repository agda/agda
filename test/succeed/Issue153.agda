{-# OPTIONS --allow-unsolved-metas #-}

-- This file documents a bug caused by one of the fixes for issue 153.

module Issue153 where

open import Common.Coinduction

record R : Set₁ where
  field
    S : Set
    T : S → Set

module D (r : R) (s : R.S r) where
  open R r

  data D (t : T s) : Set where

module M (r : R) (s : R.S r) where
  open R r
  open D _ s

  postulate
    t : T s
    d : D t

  foo : ∞ (D t)
  foo = ♯ d

-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/Interaction/Highlighting/Generate.hs:383
