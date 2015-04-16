module Arith where

open import Common.IO
open import Common.Nat
open import Common.Unit

test : Nat
test = 4

foobar : Nat -> Nat
foobar zero = zero
foobar (suc n) = suc (suc n)

main : IO Unit
main =
--  n <- readNat ,
  printNat 0 ,,
  printNat (0 + 1) ,,
  printNat (1 * 2) ,,
  printNat (suc (suc (suc (suc zero))) ∸ suc zero) ,,
  printNat test    ,,
  printNat (foobar 4) ,,
--  printNat n ,,
  return unit
