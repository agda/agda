
module Problem2 where

open import Problem1

infixr 40 _►_

data Vec (A : Set) : Nat -> Set where
  ε   : Vec A zero
  _►_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

-- 2.1

vec : {A : Set}{n : Nat} -> A -> Vec A n
vec {n = zero } x = ε
vec {n = suc n} x = x ► vec x

-- 2.2

infixl 80 _<*>_

_<*>_ : {A B : Set}{n : Nat} -> Vec (A -> B) n -> Vec A n -> Vec B n
ε        <*> ε        = ε
(f ► fs) <*> (x ► xs) = f x ► fs <*> xs

-- 2.3

map : {A B : Set}{n : Nat} -> (A -> B) -> Vec A n -> Vec B n
map f xs = vec f <*> xs

-- 2.4

zip : {A B C : Set}{n : Nat} -> (A -> B -> C) ->
      Vec A n -> Vec B n -> Vec C n
zip f xs ys = vec f <*> xs <*> ys
