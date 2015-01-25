-- Andreas, 2014-01-24, Issue 1411
-- First split might not succeed in the unifier,
-- so try later splits also.

-- {-# OPTIONS -v tc.lhs:10 #-}

open import Common.Prelude
open import Common.Equality

data Fin : Nat → Set where
  fzero : (n : Nat) → Fin (suc n)
  fsuc  : (n : Nat) → (i : Fin n) → Fin (suc n)

data _≅_ {A : Set} (a : A) : {B : Set} (b : B) → Set where
  refl : a ≅ a

works : ∀ n m (i : Fin n) (j : Fin m) → n ≡ m → fsuc n i ≅ fsuc m j → i ≅ j
works n .n i .i refl refl = refl

fails : ∀ n m (i : Fin n) (j : Fin m) → fsuc n i ≅ fsuc m j → n ≡ m → i ≅ j
fails n .n i .i refl refl = refl

-- Refuse to solve heterogeneous constraint i : Fin n =?= j : Fin m
-- when checking that the pattern refl has type fsuc n i ≅ fsuc m j

-- Should work now.
