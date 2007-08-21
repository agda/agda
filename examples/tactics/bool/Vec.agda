
module Vec where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Vec (A : Set) : Nat -> Set where
  ε   : Vec A zero
  _►_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

vec : {A : Set}{n : Nat} -> A -> Vec A n
vec {n = zero}  x = ε
vec {n = suc n} x = x ► vec x

_<*>_ : {A B : Set}{n : Nat} -> Vec (A -> B) n -> Vec A n -> Vec B n
ε        <*> ε        = ε
(f ► fs) <*> (x ► xs) = f x ► (fs <*> xs)

-- map
-- zip
