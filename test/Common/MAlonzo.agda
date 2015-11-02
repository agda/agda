
module Common.MAlonzo where

open import Common.Prelude hiding (putStrLn)
open import Common.Coinduction

{-# IMPORT Data.Text.IO #-}

postulate
  putStrLn : ∞ String → IO Unit

{-# COMPILED putStrLn Data.Text.IO.putStrLn #-}

main = putStrLn (♯ "This is a dummy main routine.")

mainPrint : String → _
mainPrint s = putStrLn (♯ s)

mainPrintNat : Nat → _
mainPrintNat n = putStrLn (♯ (natToString n))
