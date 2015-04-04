module tests.ModuleArgs where

open import Prelude.Nat
open import Prelude.IO
open import Prelude.Unit

module X (y : Nat) where
  addTo : Nat -> Nat
  addTo x = y + x

open X 23

-- should return 35
main : IO Unit
main = printNat (addTo 12)
