{-# OPTIONS --guardedness #-}

module HelloWorld where

open import IO
open import Data.String
open import Data.Unit
open import Level using (0ℓ)

main = run {0ℓ} (putStrLn "Hello World!")
