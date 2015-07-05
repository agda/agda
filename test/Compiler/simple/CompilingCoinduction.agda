
module CompilingCoinduction where

open import Common.Coinduction
open import Common.List
open import Common.Char
open import Common.String
open import Common.Unit


postulate
  IO : Set → Set

{-# COMPILED_TYPE IO IO #-}
{-# BUILTIN IO IO #-}

postulate
  putStrLn : ∞ String → IO Unit

{-# COMPILED putStrLn putStrLn #-}
{-# COMPILED_UHC putStrLn (UHC.Agda.Builtins.primPutStrLn) #-}

main = putStrLn (♯ "a")
