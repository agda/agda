-- Mixing CatchAll branches with varying arity can be tricky.
--
-- If the number of arguments a catch all branch expects to be already abstracted over is smaller
-- than the number of arguments present in the failing clause/branch, we need to apply
-- the catch-all branch to the surplus arguments already abstracted over.

module tests.CatchAllVarArity where

open import Prelude.Nat
open import Prelude.IO
open import Prelude.Unit


f : Nat → Nat → Nat
f Z = λ y → y
f (S Z) (S y) = S y
f x y = (S y)

--expected:
-- 10
-- 21
-- 1
-- 0
-- 4
-- 1
main = printNat (f 0 10) ,,
  putStrLn "" ,,
  printNat (f 10 20) ,,
  putStrLn "" ,,
  printNat (f 10 0) ,,
  putStrLn "" ,,
  printNat (f 0 0) ,,
  putStrLn "" ,,
  printNat (f 1 4) ,,
  putStrLn "" ,,
  printNat (f 1 0) ,,
  putStrLn ""

