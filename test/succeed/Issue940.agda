
{-# OPTIONS --copatterns --show-implicit #-}

module Issue940 where

module _ (A : Set) where

  record Box : Set where
    constructor box
    field
      unbox : A

  open Box

  postulate x : A

  ex : Box
  ex = box x -- works

  ex' : Box
  unbox ex' = x

  -- Error WAS:
  -- An internal error has occurred. Please report this as a bug.
  -- Location of the error: src/full/Agda/TypeChecking/Substitute.hs:326

postulate
  A : Set

ok : Box A
Box.unbox ok = x A -- works
