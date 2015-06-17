-- Checks that UHC FFI calls using non-magic datatypes work
module UHC-FFI where

data Nat : Set where
  Zero : Nat
  Suc : Nat -> Nat
{-# COMPILED_DATA_UHC Nat UHC.Agda.Builtins.Nat Zero Suc #-}

open import Common.IO
open import Common.Unit

main : IO Unit
main = putStr "Hello World"

