
module Examples where

open import Prelude
open import Star
open import Modal

El : Set -> Rel True
El A _ _ = A

List : Set -> Set
List A = Star (El A) _ _

Nat = List True

zero : Nat
zero = ε

suc : Nat -> Nat
suc n = _ • n

-- Vectors

Vec : Set -> Nat -> Set
Vec A = All (\_ -> A)

infixr 40 _::_
_::_ : {A : Set}{n : Nat} -> A -> Vec A n -> Vec A (suc n)
x :: xs = check x • xs

-- Fin

Fin : Nat -> Set
Fin = Any (\_ -> True)

-- Turning a vector to a list

vecToList : {A : Set}{n : Nat} -> Vec A n -> List A
vecToList {A} = map ! uncheck

listToVec : {A : Set}(xs : List A) -> Vec A (length xs)
listToVec  ε       = ε
listToVec (x • xs) = x :: listToVec xs

-- span

test : Vec Nat (suc (suc (suc zero)))
test = zero :: suc zero :: suc (suc zero) :: ε
