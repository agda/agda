-- Andreas, 2021-06-01, also test issue #5425

module ModuleArgs where

open import Common.Nat
open import Common.IO
open import Common.Unit

module X (y : Nat) where

  addTo : Nat → Nat
  addTo x = y + x

  data D : Set where
    c : D

open X 23

-- This used to crash `agda --js --js-optimize`
-- which could not cope with constructors from applied modules
-- (missing canonicalization of constructor names).
c' : D
c' = c

-- should return 35
main : IO Unit
main = printNat (addTo 12)
