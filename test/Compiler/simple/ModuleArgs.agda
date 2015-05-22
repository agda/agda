module ModuleArgs where

open import Common.Nat
open import Common.IO
open import Common.Unit

module X (y : Nat) where
  addTo : Nat -> Nat
  addTo x = y + x

open X 23

-- should return 35
main : IO Unit
main = printNat (addTo 12)
