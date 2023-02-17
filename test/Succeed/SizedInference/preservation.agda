-- Test for size preservation
{-# OPTIONS --no-double-check --type-based-termination #-}

module SizedInference.preservation where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data List (A : Set) : Set where
  nil  : List A
  cons : A → List A → List A

-- inferred to be size-preserving
map : ∀ {A B : Set} → (f : A → B) → List A → List B
map f nil = nil
map f (cons a b) = cons (f a) (map f b)

id : ∀ {A : Set} → A → A
id x = x

length : ∀ {A : Set} → (List A) → Nat
length nil = zero
-- we have a recursive call over a foreign function applicaiton
-- if the function is size-preserting, then the call is fine
length (cons _ xs) = suc (length (map id xs))
