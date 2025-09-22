{-# OPTIONS --guardedness #-}

open import IO
open import Data.Nat using (_+_)
open import Data.Nat.Show

main : Main
main = run (putStrLn (show (1 + 2)))
