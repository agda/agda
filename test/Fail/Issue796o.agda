-- {-# OPTIONS -v tc:10 -v tc.inj:100 #-}
-- 2013-02-18 reported by rotsor

module Issue796o where

data U : Set where
  a b : U

data A : Set where
data B : Set where

abstract
  A' B' : Set

  A' = A
  B' = B  -- fails if changed to A.  Should always fail.

[_] : U → Set
[_] a = A'
[_] b = B'

f : ∀ u → [ u ] → U
f u _ = u

postulate x : A'

zzz = f _ x
