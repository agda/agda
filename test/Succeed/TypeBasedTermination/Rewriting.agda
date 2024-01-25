-- Tests the usage of rewrites
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.Rewriting where

postulate
  bad : {A : Set} → A

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

{-# BUILTIN EQUALITY _≡_ #-}


data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

_+_ : Nat → Nat → Nat
zero  + m = m
suc n + m = suc (n + m)

modh : (k m n j : Nat) → Nat
modh k m  zero    j      = k
modh k m (suc n)  zero   = modh zero    m n m
modh k m (suc n) (suc j) = modh (suc k) m n j

+-identityʳ : (n : Nat) → (n + zero) ≡ n
+-identityʳ  = bad

+-suc : ∀ m n → (m + suc n) ≡ (suc (m + n))
+-suc = bad

modh-idem : ∀ acc a n → modh zero (acc + n) (modh acc (acc + n) a n) (acc + n) ≡ modh acc (acc + n) a n
modh-idem acc zero    n       = bad
modh-idem acc (suc a) zero    rewrite +-identityʳ acc = modh-idem zero a acc
modh-idem acc (suc a) (suc n) rewrite +-suc acc n = modh-idem (suc acc) a n
