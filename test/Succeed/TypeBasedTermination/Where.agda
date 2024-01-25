-- Tests a correct handling of a function used in a where block
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.Where where

data Bool : Set where
  true  : Bool
  false : Bool

if_then_else_ : ∀ {A : Set} → Bool → A → A → A
if true  then a else _ = a
if false then _ else a = a

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data Fin : Nat → Set where
  zero' : ∀ {n} → Fin (suc n)
  suc'  : ∀ {n} → (i : Fin n) → Fin (suc n)

data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A

map : ∀ {A B : Set} → (A → B) → List A → List B
map f nil = nil
map f (cons x xs) = cons (f x) (map f xs)

length : {A : Set} → List A → Nat
length nil = zero
length (cons _ xs) = suc (length xs)

findIndicesᵇ : {A : Set} → (A → Bool) → (xs : List A) → List (Fin (length xs))
findIndicesᵇ p nil         = nil
findIndicesᵇ p (cons x xs) = if (p x)
  then (cons zero' indices)
  else indices
    where indices = map suc' (findIndicesᵇ p xs)
