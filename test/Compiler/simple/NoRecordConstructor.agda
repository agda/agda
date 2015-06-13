
open import Common.Nat
open import Common.IO
open import Common.Unit

record Test : Set where
  field
    a b c : Nat

f : Test -> Nat
f r = a + b + c
  where open Test r

open Test

g : Nat
g = (f (record {a = 100; b = 120; c = 140})) + a m + b m + c m
  where m = record {c = 400; a = 200; b = 300}

main : IO Unit
main = printNat g

-- Expected Output: 1260
