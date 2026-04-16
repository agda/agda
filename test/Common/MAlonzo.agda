{-# OPTIONS --guardedness --level-universe #-}

module Common.MAlonzo where

open import Common.Prelude hiding (putStrLn)
open import Common.Coinduction

{-# FOREIGN GHC import qualified Data.Text.IO #-}

postulate
  putStrLn : ∞ String → IO Unit

{-# COMPILE GHC putStrLn = Data.Text.IO.putStrLn . MAlonzo.RTE.flat #-}

main = putStrLn (♯ "This is a dummy main routine.")

mainPrint : String → _
mainPrint s = putStrLn (♯ s)

mainPrintNat : Nat → _
mainPrintNat n = putStrLn (♯ (natToString n))
