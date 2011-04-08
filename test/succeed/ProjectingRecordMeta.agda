module ProjectingRecordMeta where

data _==_ {A : Set}(a : A) : A -> Set where
  refl : a == a

-- Andreas, Feb/Apr 2011
record Prod (A B : Set) : Set where
  constructor _,_ 
  field
    fst : A
    snd : B 

open Prod public

testProj : {A B : Set}(y z : Prod A B) ->
  let X : Prod A B
      X = _       -- Solution: fst y , snd z
  in (C : Set) -> (fst X == fst y -> snd X == snd z -> C) -> C
testProj y z C k = k refl refl
-- ok, Agda handles projections properly during unification

testProj' : {A B : Set}(y z : Prod A B) ->
  let X : Prod A B
      X = _       -- Solution: fst y , snd z
  in Prod (fst X == fst y) (snd X == snd z)
testProj' y z = refl , refl
