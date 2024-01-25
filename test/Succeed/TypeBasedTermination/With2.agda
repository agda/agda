-- Tests another with-function
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.With2 where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

data Prod (A B : Set) : Set where
  prod : A → B → Prod A B

unfold : ∀ {A} (P : Nat → Set)
         (f : ∀ {n} → P (suc n) → Maybe (Prod A (P n))) →
         ∀ {n} → P n → List A
unfold P f {n = zero}  s = nil
unfold P f {n = suc n} s with f s
... | nothing       = nil
... | just (prod x s') = cons x (unfold P f s')
