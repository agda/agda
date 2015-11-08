-- 2010-11-21
-- testing correct implementation of eta for records with higher-order fields

module Issue366 where

data Bool : Set where
  true false : Bool

record R (A : Set) : Set where
  constructor r
  field
    unR : A

open R

foo : Bool
foo = unR (r (unR (r (λ (_ : Bool) → false))
              true))
-- before 2010-11-21, an incorrect implementation of eta-contraction
-- reduced foo to (unR true)
-- Error message was (due to clause compilation):
-- Incomplete pattern matching

data _==_ {A : Set}(a : A) : A -> Set where
  refl : a == a

test : foo == false
test = refl

