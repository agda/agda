module Term where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data D : Nat -> Set where
  cz : D zero
  c1 : forall {n} -> D n -> D (suc n)
  c2 : forall {n} -> D n -> D n

-- To see that this is terminating the termination checker has to look at the
-- natural number index, which is in a dot pattern.
f : forall {n} -> D n -> Nat
f cz     = zero
f (c1 d) = f (c2 d)
f (c2 d) = f d

