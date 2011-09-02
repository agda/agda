
module Issue361 where

data _==_ {A : Set}(a : A) : A -> Set where
  refl : a == a

postulate
  A : Set
  a b : A
  F : A -> Set

record R (a : A) : Set where
  constructor c
  field 
    p : A

beta : (x : A) -> R.p {b} (c {b} x) == x
beta x = refl

lemma : (r : R a) -> R.p {b} (c {b} (R.p {a} r)) == R.p {a} r
lemma r = beta (R.p {a} r)
