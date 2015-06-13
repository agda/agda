{-# OPTIONS --copatterns #-}

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

r1 : Test
a r1 = 100
b r1 = 120
c r1 = 140

r2 : Test
c r2 = 400
a r2 = 200
b r2 = 300

g : Nat
g = f r1 + a m + b m + c m
  where m = r2

main : IO Unit
main = printNat g

-- Expected Output: 1260
