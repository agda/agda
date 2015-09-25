{- Andreas, 2013-02-18 recursive meta occurrence no longer throws error{-# OPTIONS --allow-unsolved-metas #-}
-- The option is supplied to force a real error to pass the regression test.
-}
module StronglyRigidOccurrence where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data _≡_ {A : Set}(a : A) : A -> Set where
  refl : a ≡ a

test : let X : Nat; X = _ in X ≡ suc X
test = refl
-- this gives an error in the occurs checker
