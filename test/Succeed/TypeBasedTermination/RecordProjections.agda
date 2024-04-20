-- Regression test for https://github.com/agda/agda/pull/7152#issuecomment-2061418950
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}

module TypeBasedTermination.RecordProjections where

open import Common.Level

postulate
  A : Set
  a : A
  P : (A : Set) → A → Set

data D (_ : A) : Set where

module _ (_ _ : D a) where

  record R (a : Level) (A : Set a) : Set a where
    field
      f : A → A

  postulate
    g : (A : Set) → R lzero A

  module M (a : Level) (A : Set a) (r : R a A) where

    h : A → A
    h = R.f r

  i : (A : Set) (r : R lzero A) (x : A) →
      let open M lzero A r in
      R lzero (P A (h x))
  i A r x = g (P A _)