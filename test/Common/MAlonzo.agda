
module Common.MAlonzo where

open import Common.Prelude
open import Common.Coinduction

postulate
  putStrLn : ∞ String → IO Unit

{-# COMPILED putStrLn putStrLn #-}

main = putStrLn (♯ "This is a dummy main routine.")

mainPrint : String → _
mainPrint s = putStrLn (♯ s)

postulate
  natToString : Nat → String

{-# COMPILED natToString show #-}

mainPrintNat : Nat → _
mainPrintNat n = putStrLn (♯ (natToString n))
