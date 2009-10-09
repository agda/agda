module Main where

-- Ensure that the entire library is compiled.
import README

open import Data.Unit
open import IO

main = run (putStrLn "Hello, world!")
