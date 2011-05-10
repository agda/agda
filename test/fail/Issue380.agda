-- Andreas, 2011-05-10
-- {-# OPTIONS -v tc.term.con:20 -v tc.meta:20 #-}
module Issue380 where

data _==_ {A : Set}(a : A) : A -> Set where
  refl : a == a

record Sigma (A : Set)(B : A -> Set) : Set where
  constructor _,_ 
  field
    fst : A
    snd : B fst
open Sigma public

testProj : {A : Set}{B : A -> Set}(y z : Sigma A B) ->
  let X : Sigma A B
      X = _ 
  in fst X == fst y -> snd X == snd z
testProj y z = refl , refl
{-  OLD BEHAVIOR: Error message about telescope comparison unreadable
This ill-typed term produces a weird error message:
(z' : fst (fst z , _283 y z) == fst y) !=<
when checking that the expression refl , refl has type
fst (fst z , _283 y z) == fst y → snd (fst z , _283 y z) == snd z
-}
{- FIXED.  Now it should complain that
Sigma (_47 y z == _47 y z) (_45 y z) !=<
fst (fst z , _43 y z) == fst y → snd (fst z , _43 y z) == snd z
when checking that the expression refl , refl has type
fst (fst z , _43 y z) == fst y → snd (fst z , _43 y z) == snd z
-}