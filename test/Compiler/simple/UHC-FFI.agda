-- Checks that UHC FFI calls using non-magic datatypes work
module UHC-FFI where

data Nat : Set where
  Zero : Nat
  Suc : Nat -> Nat
{-# COMPILED_DATA_UHC Nat UHC.Agda.Builtins.Nat Zero Suc #-}

{-# IMPORT_UHC Data.Char #-}

open import Common.IO
open import Common.Unit
open import Common.String
open import Common.Char


postulate toLower : Char -> Char
{-# COMPILED_UHC toLower Data.Char.toLower #-}

main : IO Unit
main = putStr (charToStr (toLower 'A'))

