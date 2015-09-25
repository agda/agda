postulate
  I : Set
  D : I → Set
  T : Set

record R : Set where
  field
    t0   : T
    {i0} : I
    t1   : T
    d0   : D i0
    {i1} : I
    d1   : D i1
    t2   : T

module M0 where
  postulate
    t0 t1 : T

module MI where
  postulate
    i1 : I
    d1 : D i1

module MD {i0 : I} where
  postulate
    d0 : D i0
    t0 : T

r : R
r = record { M0; t2 = M0.t0; MD; MI; i0 = i0 }
  module My where postulate i0 : I

r' : R
r' = record { R r; t0 = R.t1 r }
  where module Rr = R r
