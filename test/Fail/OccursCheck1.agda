-- Andreas, 2012-05-04
-- Occurs check when unifying indices in patterns
{- Andreas, 2013-02-18 recursive meta occurrence no longer throws error
{-# OPTIONS --allow-unsolved-metas #-}
-- The option is supplied to force a real error to pass the regression test.
-}
module OccursCheck1 where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

test :
  let X : Nat
      X = _
  in  X == suc X
test = refl
-- should fail with error message indicating no solution possible
