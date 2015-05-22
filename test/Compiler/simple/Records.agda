module Records where

open import Common.Nat
open import Common.IO
open import Common.Unit

record Test : Set where
  constructor mkTest
  field
    a b c : Nat

f : Test -> Nat
f (mkTest a b c) = a + b + c

open Test

g : Nat
g = (f (mkTest 34 12 54)) + (f (record {a = 100; b = 120; c = 140})) + a m + b m + c m
  where m = mkTest 200 300 400

main : IO Unit
main = printNat g
