
module CompilingCoinduction where

open import Common.Coinduction
open import Common.Char
open import Common.String

data Unit : Set where
  unit : Unit

{-# COMPILED_DATA Unit () () #-}

postulate
  IO : Set → Set

{-# COMPILED_TYPE IO IO #-}
{-# BUILTIN IO IO #-}

{-# IMPORT Data.Text.IO #-}

postulate
  putStrLn : ∞ String → IO Unit

{-# COMPILED putStrLn Data.Text.IO.putStrLn #-}
{-# COMPILED_UHC putStrLn (UHC.Agda.Builtins.primPutStrLn) #-}

main = putStrLn (♯ "a")
