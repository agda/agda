module tests.Forcing2 where

open import Prelude.Nat
open import Prelude.IO
open import Prelude.Unit

data _**_ (A B : Set) : Set where
  _,_ : A -> B -> A ** B

data P {A B : Set} : A ** B -> Set where
  _,_ : (x : A)(y : B) -> P (x , y)

data Q {A : Set} : A ** A -> Set where
  [_] : (x : A) -> Q (x , x)

test1 : (p : Nat ** Nat) -> P p -> Nat
test1 .(x , y) (x , y) = x + y

test2 : (q : Nat ** Nat) -> Q q -> Nat
test2 .(x , x) [ x ]  = ((S (S Z)) * x) + 1


test3 : (q : (Nat ** Nat) ** (Nat ** Nat)) -> Q q -> Nat
test3 .((Z , Z)   , (Z , Z))   [ Z   , Z ]  = Z
test3 .((S n , m) , (S n , m)) [ S n , m ]  = S n + m
test3 .((Z , m)   , (Z , m))   [ Z   , m ]  = m
main : IO Unit 
main = 
    printNat (test1 (5  , 8) (5  , 8)) ,,
    printNat (test2 (1 , 1) [ 1 ])     ,,
    printNat (test3 ( (3 , 4) , (3 , 4) ) [ 3 , 4 ]) ,,
    return unit
