-- Andreas, 2012-01-11
module Issue551b where

data Box (A : Set) : Set where
  [_] : .A → Box A

implicit : {A : Set}{{a : A}} -> A
implicit {{a}} = a

postulate
  A : Set
  .a : A  

a' : Box A
a' = [ implicit ]
-- this should succeed

f : {X : Set} → Box X → Box (Box X)
f [ x ] = [ [ implicit ] ]
-- this as well