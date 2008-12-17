module Acc where

data Rel(A : Set) : Set1 where
  rel : (A -> A -> Set) -> Rel A

_is_than_ : {A : Set} -> A -> Rel A -> A -> Set
x is rel f than y = f x y

data Acc {A : Set} (less : Rel A) (x : A)  : Set where
  acc : ((y : A) -> x is less than y -> Acc less y) -> Acc less x

data WO {A : Set} (less : Rel A) : Set where
  wo : ((x : A) -> Acc less x) -> WO less

data False : Set where
data True : Set where
  tt : True

data Nat : Set where
  Z : Nat
  S : Nat -> Nat


data ∏ {A : Set} (f : A -> Set) : Set where
  ∏I : ((z : A) -> f z) -> ∏ f


data Ord : Set  where
  z : Ord
  lim : (Nat -> Ord) -> Ord

zp  : Ord -> Ord
zp z = z
zp (lim f) = lim (\x -> zp (f x))


_<_ : Ord -> Ord -> Set
z < _ = True
lim _ < z = False
lim f < lim g = ∏ \(n : Nat) -> f n < g n

ltNat : Nat -> Nat -> Set
ltNat Z Z = False
ltNat Z (S n) = True
ltNat (S m) (S n) = ltNat m n
ltNat (S m) Z = False

ltNatRel : Rel Nat
ltNatRel = rel ltNat

postulate woltNat : WO ltNatRel
