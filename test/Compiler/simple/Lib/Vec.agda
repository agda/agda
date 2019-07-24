module Lib.Vec where

open import Common.Nat
open import Lib.Fin
open import Common.Unit
import Common.List as List; open List using (List ; [] ; _∷_)

data Vec (A : Set) :  Nat → Set where
  _∷_ : {n : Nat} → A → Vec A n → Vec A (suc n)
  []  : Vec A zero

infixr 30 _++_

_++_ : {A : Set}{m n : Nat} → Vec A m → Vec A n → Vec A (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

snoc : {A : Set}{n : Nat} → Vec A n → A → Vec A (suc n)
snoc []       e = e ∷ []
snoc (x ∷ xs) e = x ∷ snoc xs e

-- Recursive length.

length : {A : Set}{n : Nat} → Vec A n → Nat
length [] = zero
length (x ∷ xs) = 1 + length xs

length' : {A : Set}{n : Nat} → Vec A n → Nat
length' {n = n} _ = n

zipWith3 : ∀ {A B C D n} → (A → B → C → D) → Vec A n → Vec B n → Vec C n → Vec D n
zipWith3 f []       []       []       = []
zipWith3 f (x ∷ xs) (y ∷ ys) (z ∷ zs) = f x y z ∷ zipWith3 f xs ys zs

zipWith : ∀ {A B C n} → (A → B → C) → Vec A n → Vec B n → {u : Unit} → Vec C n
zipWith _ [] [] = []
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys {u = unit}

_!_ : ∀ {A n} → Vec A n → Fin n → A
(x ∷ xs) ! fz   = x
(_ ∷ xs) ! fs n = xs ! n
[] ! ()

-- Update vector at index

_[_]=_ : {A : Set}{n : Nat} → Vec A n → Fin n → A → Vec A n
(a ∷ as) [ fz   ]= e = e ∷ as
(a ∷ as) [ fs n ]= e = a ∷ (as [ n ]= e)
[] [ () ]= e

map : ∀ {A B n}(f : A → B)(xs : Vec A n) → Vec B n
map f []        = []
map f (x ∷ xs) = f x ∷ map f xs

-- Vector to List, forget the length.

forgetL : {A : Set}{n : Nat} → Vec A n → List A
forgetL []       = []
forgetL (x ∷ xs) = x ∷ forgetL xs

-- List to Vector, "rem"member the length.

rem : {A : Set}(xs : List A) → Vec A (List.length xs)
rem [] = []
rem (x ∷ xs) = x ∷ rem xs
