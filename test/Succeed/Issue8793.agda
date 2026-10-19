-- With --experimental-irrelevance the variable bound by an irrelevant
-- Pi is shape-irrelevant in the codomain, so it may be used in a
-- shape-irrelevant argument there.  The occurs check treated it as
-- irrelevant, so no metavariable could be solved with such a type.

{-# OPTIONS --experimental-irrelevance #-}

module Issue8793 where

postulate
  A : Set
  B : ..(x : A) → Set

-- Accepted.
T : Set
T = .(x : A) → B x

record R (X : Set) : Set₁ where
  field out : Set

D : Set₁
D = R (.(x : A) → B x)

test : D → Set
test r = R.out r

-- Error was:
-- Failed to solve the following constraints:
--   .(x : A) → B x =< _X_6 : Set (blocked on _X_6)
