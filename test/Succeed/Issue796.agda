-- 2013-02-21 Andreas
-- ensure that constructor-headedness works also for abstract things
module Issue796 where

data U : Set where
  a b : U

data A : Set where
data B : Set where

abstract
  A' B' : Set

  A' = A
  B' = B  -- fails if changed to A.

  [_] : U → Set
  [_] a = A'
  [_] b = B'

  f : ∀ u → [ u ] → U
  f u _ = u

  postulate x : A'

  zzz = f _ x
  -- succeeds since [_] is constructor headed
