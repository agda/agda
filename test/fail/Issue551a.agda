-- Andreas, 2012-01-11
module Issue551a where

data Box (A : Set) : Set where
  [_] : A → Box A

implicit : {A : Set}{{a : A}} -> A
implicit {{a}} = a

postulate
  A : Set
  .a : A  -- this irrelevant definition needs to be ignored by instance search

a' : Box A
a' = [ implicit ]
-- this should fail