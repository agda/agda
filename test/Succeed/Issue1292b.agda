-- Andreas, 2014-10-05
-- Andreas, 2026-10-12: merge in LibSucceed/Termination/Sized/SizedNat(Annotated).agda

{-# OPTIONS --sized-types #-}
{-# OPTIONS --cubical-compatible -WnoUnsupportedIndexedMatch #-}

module _ where

open import Agda.Builtin.Size

module ExplicitSizes where

  data Nat : (i : Size) → Set where
    zero : (i : Size) → Nat (↑ i)
    suc  : (i : Size) → Nat i → Nat (↑ i)

  -- subtraction is non size increasing
  sub : (i : Size) → Nat i → Nat ∞ → Nat i
  sub .(↑ i) (zero i)  n         = zero i
  sub .(↑ i) (suc i m) (zero _)  = suc i m
  sub .(↑ i) (suc i m) (suc _ n) = sub i m n

  -- div' m n  computes  ceiling(m/(n+1))
  div' : (i : Size) → Nat i → Nat ∞ → Nat i
  div' .(↑ i) (zero i)  n = zero i
  div' .(↑ i) (suc i m) n = suc  i (div' i (sub i m n) n)

module ImplicitSizes where

  data Nat : Size → Set where
    zero : {size : Size} → Nat (↑ size)
    suc  : {size : Size} → Nat size → Nat (↑ size)

  -- subtraction is non size increasing
  sub : {size : Size} → Nat size → Nat ∞ → Nat size
  sub zero    n       = zero
  sub (suc m) zero    = suc m
  sub (suc m) (suc n) = sub m n

  -- div' m n  computes  ceiling(m/(n+1))
  div' : {size : Size} → Nat size → Nat ∞ → Nat size
  div' zero    n = zero
  div' (suc m) n = suc (div' (sub m n) n)

  -- Cap natural numbers at 1 (size preserving)

  cap1 : {i : Size} → Nat i → Nat i
  cap1 zero = zero
  cap1 (suc zero) = suc zero
  cap1 (suc (suc _)) = suc zero

-- Should termination check even with --cubical-compatible
