
-- When checking pattern coverage we might end up having to split
-- on a dot pattern (if the individual clauses split differently).
-- This is fine as long as the dot pattern is on constructor form.
module SplitOnDotPattern where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Vec (A : Set) : Nat -> Set where
  []   : Vec A zero
  _::_ : forall {n} -> A -> Vec A n -> Vec A (suc n)

rev : forall {A n m} -> Vec A n -> Vec A m -> Vec A m
rev             []        ys = ys
rev {n = suc n} (x :: xs) ys = ys

