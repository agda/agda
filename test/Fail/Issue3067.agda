
data A : Set where
  consA : A → A

A-false : {Y : Set} → A → Y
A-false (consA b) = A-false b

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

A-on-Nat : A → Nat → Nat
A-on-Nat σ zero = A-false σ
A-on-Nat σ (suc t) = suc (A-on-Nat σ t)

module _
  (any : {X : Set} → X)
  (P : Nat → Set)
  (p : (n : Nat) → P n → P (suc n))
  (eternity : (a : A) (n : Nat) → P (A-on-Nat (A-false a) n))
  where

  A-loop-term : (a : A) (n : Nat) → P (A-on-Nat a n)
  A-loop-term a zero = any
  A-loop-term a (suc n) = p _ (eternity _ n)
