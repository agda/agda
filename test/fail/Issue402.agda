module Issue402 where

record Unit : Set where
  constructor inn
  field
    out : Unit

data _==_ {A : Set}(a : A) : A -> Set where
  refl : a == a

test : (x y : Unit) -> x == y
test x y = refl

-- this used to cause an infinite loop in the conversion checker
-- now it fails, because no eta-laws are generated for the
-- unguarded recursive record Unit
