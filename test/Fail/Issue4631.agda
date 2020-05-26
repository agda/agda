record R0 : Set₁ where
  constructor c0
  field f0 : Set

record R1 : Set₁ where
  constructor c1
  field f1 : R0

test : R1 → Set₁
test x@(c1 x) = Set
