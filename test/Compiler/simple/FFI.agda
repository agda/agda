module FFI where

open import Common.Prelude


_+'_ : Nat → Nat → Nat
zero +' y = y
suc x +' y = suc (x +' y)
{-# COMPILED _+'_ ((+) :: Integer -> Integer -> Integer) #-}

-- on-purpose buggy haskell implementation!
_+''_ : Nat → Nat → Nat
zero +'' y = y
suc x +'' y = suc (x +'' y)
{-# COMPILED _+''_ ((-) :: Integer -> Integer -> Integer) #-}


open import Common.IO
open import Common.Unit

main : IO Unit
main = printNat (10 +' 5) ,,
  printNat (30 +'' 7)

