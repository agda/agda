module Nat where

data Rel (A : Set) : Set1 where
  rel : (A -> A -> Set) -> Rel A

_is_than_ : {A : Set} -> A -> Rel A -> A -> Set
x is rel f than y = f x y

data Acc {A : Set} (less : Rel A) (x : A) : Set where
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



ltNat : Nat -> Nat -> Set
ltNat Z Z = False
ltNat Z (S n) = True
ltNat (S m) (S n) = ltNat m n
ltNat (S m) Z = False

ltNatRel : Rel Nat
ltNatRel = rel ltNat

postulate woltNat : WO ltNatRel

idN : Nat -> Nat
idN x = x

id  : {A : Set} -> A -> A
id x = x

down1 : Nat -> Nat
down1 Z = Z
down1 (S n) = down1 n

-- measure down1 = (woNat, id)
-- For a function f : (x:A) -> B(x)
-- f(p) = ... f(x1) ... f(x2)
-- measure_set : Set
-- measure_rel : Rel measure_set
-- measure_ord : WO measure_rel
-- measure_fun : A -> measure_set
-- For j-th call of f in i-th clause of f:
-- measure_i_j_hint : xj is measure_rel than p

data Measure : Set1 where
  μ : {M : Set} -> {rel : Rel M} -> (ord : WO rel) -> Measure

{-
down1_measure_set : Set
down1_measure_set = Nat
down1_measure_rel : Rel down1_measure_set
down1_measure_rel = ltNatRel
down1_measure_ord : WO measure_rel
down1_measure_ord = woltNat
-}
down1-measure : Measure
down1-measure = μ woltNat

down1-2-1-hint : (n : Nat) -> n is ltNatRel than (S n)
down1-2-1-hint Z = tt
down1-2-1-hint (S n) = down1-2-1-hint n

{-
down2 : Nat -> Nat
down2 Z = Z
down2 (S n) = down2 (idN n)

down3 : Nat -> Nat
down3 Z = Z
down3 (S n) = down3 (id n)

plus : Nat -> Nat -> Nat
plus Z n = n
plus (S m) n = S(plus m n)
-}

