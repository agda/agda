-- {-# OPTIONS -v tc.meta:100 #-}
-- Andreas, 2011-09-21 (fix by Ulf)
module Issue458b where

data _≡_ {A : Set}(a : A) : A -> Set where
  refl : a ≡ a

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Pair (A B : Set) : Set where
  pair : A -> B -> Pair A B

fst : {A B : Set} -> Pair A B -> A
fst (pair a b) = a

overzeal : let X : Nat -> Nat -> Nat
               X = _
               Y : Pair Nat Nat -> Nat
               Y = _
           in {C : Set} ->   
              (({x y : Nat}        -> X x x ≡ Y (pair x y)) ->
               ({z : Pair Nat Nat} -> Y z ≡ fst z)          -> 
               ({x y : Nat}        -> X x y ≡ x)            -> C) -> C
overzeal k = k refl refl refl
-- This should succeed.
-- However, before Ulf's fix the first constraint would lead to
-- a pruning of y from Y, since X does not depend on y
-- This lost the solution Y = fst.
{- ERROR was:
Cannot instantiate the metavariable _59 to (fst .z) since it
contains the variable .z which is not in scope of the metavariable
when checking that the expression refl has type (_59 ≡ fst .z)
-}
