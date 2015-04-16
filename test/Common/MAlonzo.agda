
module Common.MAlonzo where

open import Common.Prelude hiding (putStrLn)
open import Common.Coinduction

postulate
  putStrLn : ∞ String → IO Unit

{-# COMPILED putStrLn putStrLn #-}

main = putStrLn (♯ "This is a dummy main routine.")

mainPrint : String → _
mainPrint s = putStrLn (♯ s)

mainPrintNat : Nat → _
mainPrintNat n = putStrLn (♯ (natToString n))
