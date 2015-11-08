-- Andreas, 2012-01-11
module Issue551b where

data Box (A : Set) : Set where
  [_] : .A → Box A

implicit : {A : Set}{{a : A}} -> A
implicit {{a}} = a

postulate
  A B : Set
  instance a : A

a' : Box A
a' = [ implicit ]
-- this should succeed

f : Box B → Box (Box B)
f [ x ] = [ [ x ] ]
-- this as well
