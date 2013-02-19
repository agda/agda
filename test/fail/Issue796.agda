-- 2013-02-18 reported by rotsor

module Issue796 where

data U : Set where
  a b : U

data A : Set where
data B : Set where

module Abs where
 abstract
  A' B' : Set

  A' = A
  B' = B

module Conc where

  open Abs

  -- Andreas, 2013-02-19
  -- this function should not be injective, since here
  -- it is not known whether A' and B' are actually different
  [_] : U → Set
  [_] a = A'
  [_] b = B'

  f : ∀ u → [ u ] → U
  f u _ = u

  postulate x : A'

  zzz = f _ x
