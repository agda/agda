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

-- There was a bug with dot patterns having the wrong context which manifested
-- itself in the following example.
data P : Nat -> Nat -> Set where
  c  : forall {d r} -> P d r -> P (suc d) r
  c' : forall {d r} -> P d r -> P d r

g : forall {d r} -> P d r -> Nat
g .{suc d} {r} (c {d} .{r} x) = g (c' x)

