
-- This module explains how to combine elimination of empty types with pattern
-- match style definitions without running into problems with decidability.

module Introduction.Data.Empty where

-- First we introduce an empty and a singleton type.
data Zero : Set where
data One  : Set where
  one : One

-- There is a special pattern () which matches any element of an (obviously)
-- empty type. If there is a ()-pattern in a left-hand side the right-hand side
-- can be omitted.
elim-Zero : {A : Set} -> Zero -> A
elim-Zero ()

data _×_ (A B : Set) : Set where
  pair : A -> B -> A × B

-- The algorithm for checking if a type is empty is very naive. In this example
-- you cannot replace pair () _ with () because the type checker cannot see
-- that Zero × B is empty.
elim-EmptyPair : {A B : Set} -> Zero × B -> A
elim-EmptyPair (pair () _)

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

-- For some empty types finite unfolding is not enough.
ConstZero : Nat -> Set
ConstZero  zero   = Zero
ConstZero (suc n) = ConstZero n

-- We can still define the elimination function but we have to do it
-- recursively over the n.
elim-ConstZero : (n : Nat) -> ConstZero n -> {A : Set} -> A
elim-ConstZero  zero   ()
elim-ConstZero (suc n)  x = elim-ConstZero n x

