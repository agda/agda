-- {-# OPTIONS -v tc.meta:100 #-}
-- Andreas, 2011-04-20
-- see Abel Pientka TLCA 2011
module PruningNonMillerPattern where

data _≡_ {A : Set}(a : A) : A -> Set where
  refl : a ≡ a

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

test : let X : Nat -> Nat -> Nat
           X = _
           Y : Nat -> Nat -> Nat
           Y = _
       in  (C : Set) -> 
           (({x y : Nat} -> X x x ≡ suc (Y x y)) ->
            ({x y : Nat} -> Y x x ≡ x)           ->
            ({x y : Nat} -> X (Y x y) y ≡ X x x) -> C) -> C
test C k = k refl refl refl
{- none of these equations is immediately solvable.  However,
   from 1. we deduce that Y does not depend on its second argument, thus
   from 2. we solve Y x y = x, and then
   eqn. 3. simplifies to X x y = X x x, thus, X does not depend on its second arg,
   we can then solve using 1.  X x y = suc x
-}

-- a variant, where pruning is even triggered from a non-pattern
test' : let X : Nat -> Nat -> Nat
            X = _
            Y : Nat -> Nat -> Nat
            Y = _
        in  (C : Set) -> 
            (({x y : Nat} -> X x (suc x) ≡ suc (Y x y)) ->  -- non-pattern lhs
             ({x y : Nat} -> Y x x ≡ x)           ->
             ({x y : Nat} -> X (Y x y) y ≡ X x x) -> C) -> C
test' C k = k refl refl refl
