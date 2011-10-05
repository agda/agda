module Prelude.Vec where

open import Prelude.Nat
open import Prelude.Fin
open import Prelude.Unit
open import Prelude.List using (List ; [] ; _::_)
infixr 40 _::_

data Vec (A : Set) :  Nat -> Set where
  _::_ : forall {n} -> A -> Vec A n -> Vec A (S n)
  []   : Vec A Z

infixr 30 _++_

_++_ : {A : Set}{m n : Nat} -> Vec A m -> Vec A n -> Vec A (m + n)
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys) 

snoc : {A : Set}{n : Nat} -> Vec A n -> A -> Vec A (S n)
snoc []        e = e :: []
snoc (x :: xs) e = x :: snoc xs e

length : {A : Set}{n : Nat} -> Vec A n -> Nat
length [] = Z
length (x :: xs) = 1 + length xs

length' : {A : Set}{n : Nat} -> Vec A n -> Nat
length' {n = n} _ = n

zipWith3 : ∀ {A B C D n} -> (A -> B -> C -> D) -> Vec A n -> Vec B n -> Vec C n -> Vec D n
zipWith3 f []        []        []        = []
zipWith3 f (x :: xs) (y :: ys) (z :: zs) = f x y z :: zipWith3 f xs ys zs

zipWith : ∀ {A B C n} -> (A -> B -> C) -> Vec A n -> Vec B n -> {u : Unit} -> Vec C n
zipWith _ [] [] = []
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys {u = unit}

_!_ : ∀ {A n} -> Vec A n -> Fin n -> A
x :: xs ! fz = x
_ :: xs ! fs n = xs ! n
[] ! ()

_[_]=_ : {A : Set}{n : Nat} -> Vec A n -> Fin n -> A -> Vec A n
(a :: as) [ fz ]= e = e :: as
(a :: as) [ fs n ]= e = a :: (as [ n ]= e)
[] [ () ]= e

map : ∀ {A B n}(f : A -> B)(xs : Vec A n) -> Vec B n
map f []        = []
map f (x :: xs) = f x :: map f xs

forgetL : {A : Set}{n : Nat} -> Vec A n -> List A
forgetL [] = []
forgetL (x :: xs) = x :: forgetL xs

rem : {A : Set}(xs : List A) -> Vec A (Prelude.List.length xs)
rem [] = []
rem (x :: xs) = x :: rem xs