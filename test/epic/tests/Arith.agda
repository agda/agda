module tests.Arith where

open import Prelude.IO
open import Prelude.Nat
open import Prelude.Unit

test : Nat
test = 4

foobar : Nat -> Nat
foobar Z = Z
foobar (S n) = S (S n)

main : IO Unit
main =
--  n <- readNat ,
  printNat 0 ,,
  printNat (0 + 1) ,,
  printNat (1 * 2) ,,
  printNat (S (S (S (S Z))) - S Z) ,,
  printNat test    ,,
  printNat (foobar 4) ,,
--  printNat n ,,
  return unit