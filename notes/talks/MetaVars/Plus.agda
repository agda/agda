
module Plus where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

infixr 40 _+_
infix  10 _==_

_+_ : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)

data _==_ (x, y : Nat) : Set where
  -- ...

postulate
  refl : {n : Nat} -> n == n
  cong : (f : Nat -> Nat){n, m : Nat} -> n == m -> f n == f m

plusZero : {n : Nat} -> n + zero == n
plusZero {zero}  = refl
plusZero {suc n} = cong suc plusZero

