{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.BadSizePreservation where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

shift_case : Maybe Nat → Maybe Nat
shift_case nothing = nothing
shift_case (just zero) = nothing
shift_case (just (suc x)) = just x

-- Should not be size preserving
shift : (Nat → Maybe Nat) → (Nat → Maybe Nat)
shift f n = shift_case (f (suc n))

inc : Nat → Maybe Nat
inc n = just (suc n)

-- This is luckily not recognized as size preserving
shift_inc : Nat → Maybe Nat
shift_inc n = shift inc n

-- Should be rejected
test : Maybe Nat → Maybe Nat
test nothing = nothing
test (just zero) = nothing
test (just (suc n)) = test (shift inc n)

-- Don't normalize this!
diverge : Maybe Nat
diverge = test (just (suc zero))
