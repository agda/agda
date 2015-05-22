module TrailingImplicits where

-- see also https://lists.chalmers.se/pipermail/agda-dev/2015-January/000041.html

open import Common.IO
open import Common.Unit
open import Common.Nat

f : (m : Nat) {l : Nat} -> Nat
f zero {l = l} = l
f (suc y) = y

main : IO Unit
main = printNat (f 0 {1}) ,,
  putStr "\n" ,,
  printNat (f 30 {1})
