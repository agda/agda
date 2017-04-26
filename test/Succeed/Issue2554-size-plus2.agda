-- Andreas, 2017-04-26
-- Allow more flexible size assignment.

module _ where

open import Agda.Builtin.Size

module ZeroZero where

  data Nat : Size → Set where
    zero : ∀{i}         → Nat i   -- does not have to be ↑ i
    suc  : ∀{i} → Nat i → Nat (↑ i)

  mon : ∀{i}{j : Size< i} → Nat j → Nat i
  mon x = x

  minus : ∀{i} → Nat i → Nat ω → Nat i
  minus x       zero    = x
  minus zero    (suc y) = zero
  minus (suc x) (suc y) = minus x y

  div : ∀{i} → Nat i → Nat ω → Nat i
  div zero y = zero
  div (suc x) y = suc (div (minus x y) y)

module DSuc where

  -- Here, the upper least bound for the size is the number itself.

  data Nat : Size → Set where
    zero : ∀{i}         → Nat i
    suc  : ∀{i} → Nat i → Nat (↑ i)
    dsuc : ∀{i} → Nat i → Nat (↑ ↑ i)

  -- Testing subtyping.

  mon : ∀{i}{j : Size< i} → Nat j → Nat i
  mon x = x

  minus : ∀{i} → Nat i → Nat ω → Nat i
  minus x        zero     = x
  minus zero     y        = zero
  minus (suc x)  (suc y)  = minus x y
  minus (suc x)  (dsuc y) = minus x (suc y)
  minus (dsuc x) (suc y)  = minus (suc x) y
  minus (dsuc x) (dsuc y) = minus x y

  div : ∀{i} → Nat i → Nat ω → Nat i
  div zero     y = zero
  div (suc x)  y = suc (div (minus x y) y)
  div (dsuc x) y = suc (div (minus (suc x) y) y)
