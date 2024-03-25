-- Tests pattern-matching on refl
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.Refl where


data Nat : Set where
  zero : Nat
  suc : Nat → Nat

data Eq {A : Set} (a : A) : A → Set where
  refl : Eq a a

data Leq : Nat → Nat → Set where
  zn : ∀ {n : Nat} → Leq zero n
  ss : ∀ {n m : Nat} → Leq n m → Leq (suc n) (suc m)

rrf : ∀ (n m : Nat) → Eq n m → Leq n m
rrf zero m refl = zn
rrf (suc n) m refl = ss (rrf n n refl)
