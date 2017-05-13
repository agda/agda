module Issue2579.Instance (A : Set) (a : A) where

open import Issue2579.Import

instance
  w : Wrap A
  w = wrap a
