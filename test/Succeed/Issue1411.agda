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

postulate
  inj-Fin-≅ : ∀ {n m} {i : Fin n} {j : Fin m} → i ≅ j → n ≡ m

suc-injective : ∀ n m (i : Fin n) (j : Fin m) → fsuc n i ≅ fsuc m j → i ≅ j
suc-injective n m i j p with inj-Fin-≅ p
suc-injective n .n i .i refl | refl = refl

-- Splitting of p fails:

-- Refuse to solve heterogeneous constraint i : Fin n =?= j : Fin m
-- when checking that the pattern refl has type fsuc n i ≅ fsuc m j

-- But the type of p is homogeneous:

-- p : fsuc n i ≅ fsuc n j
-- j : Fin n
-- i : Fin n
-- n : Nat

-- Should work now.
