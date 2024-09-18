module Arith where

open import Common.IO
open import Common.Nat renaming (_∸_ to _-_)  -- workaround for #1855
open import Common.Unit
open import Agda.Builtin.String using (primShowNat)

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
  printNat (suc (suc (suc (suc zero))) - suc zero) ,,
  putStr (primShowNat test) ,,  -- PR #7500, primShowNat used to crash in JS
  printNat (foobar 4) ,,
--  printNat n ,,
  return unit
