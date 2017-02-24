-- Checks that UHC FFI calls using non-magic datatypes work
module UHC-FFI where

data Nat : Set where
  Zero : Nat
  Suc : Nat -> Nat
{-# COMPILE UHC Nat = data UHC.Agda.Builtins.Nat (Zero | Suc) #-}

{-# FOREIGN UHC __IMPORT__ Data.Char #-}

open import Common.IO
open import Common.Unit
open import Common.String
open import Common.Char


postulate toLower : Char -> Char
{-# COMPILE UHC toLower = Data.Char.toLower #-}

main : IO Unit
main = putStr (charToStr (toLower 'A'))

