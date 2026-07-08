{-# OPTIONS --smart-with #-}

open import Agda.Builtin.Nat hiding (_==_)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

data ⊥ : Set where

data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : (A → ⊥) → Dec A

postulate
  _≡?_ : (n m : Nat) → Dec (n ≡ m)

-- This use of '--smart-with' technically fails the on-paper criteria
-- ('no p' contains a closure) but in the Agda implementation, we allow
-- eta-contracted functions on the RHS

_==_ : (n m : Nat) → Bool
n == m with n ≡? m
... | yes p = true
... | no  p = false
