module tests.VaryingClauseArity where

-- see also thread https://lists.chalmers.se/pipermail/agda-dev/2015-January/000041.html

open import Prelude.IO
open import Prelude.Unit
open import Prelude.Nat


Sum : Nat → Set
Sum 0       = Nat
Sum (S n) = Nat → Sum n

sum : (acc : Nat) (n : Nat) → Sum n
sum acc 0         = acc
sum acc (S n) 0 = sum acc n
sum acc (S n) m = sum (m + acc) n

-- expected:
-- 10
-- 20
-- 33
main : IO Unit
main = printNat (sum 10 0) ,,
  putStr "\n" ,,
  printNat (sum 20 1 0) ,,
  putStr "\n" ,,
  printNat (sum 30 1 3)
