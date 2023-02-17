-- Testing heavy dependency between types
{-# OPTIONS --type-based-termination --no-double-check #-}
module SizedInference.dependency where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data Fin : Nat → Set where
  zero' : ∀ {n} → Fin (suc n)
  suc'  : ∀ {n} → (i : Fin n) → Fin (suc n)

data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A

length : ∀ {A : Set} → List A → Nat
length nil = zero
length (cons _ xs) = suc (length xs)

id : ∀ {A : Set} → A → A
id x = x

lookup : ∀ {A : Set} → (xs : List A) → Fin (length xs) → A
lookup (cons x xs) zero'    = x
lookup (cons x xs) (suc' i) = lookup xs (id i)
