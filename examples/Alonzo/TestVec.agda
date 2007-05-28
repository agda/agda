module TestVec where
open import PreludeNatType
open import PreludeShow

infixr 40 _::_

data Vec (A : Set) : Nat -> Set where
    []   : Vec A zero
    _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

head : {A : Set}{n : Nat} -> Vec A (suc n) -> A
head (x :: _) = x  -- no need for a [] case

length : {A : Set}{n : Nat} -> Vec A n -> Nat
length {A} {n} v = n

three : Vec Nat 3
three = 1 :: 2 :: 3 :: []

mainS = showNat (length  three)