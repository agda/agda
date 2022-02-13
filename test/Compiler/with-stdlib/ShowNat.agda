{-# OPTIONS --guardedness #-}

module ShowNat where

open import IO
open import Data.Unit
open import Data.Nat.Show
open import Level using (0ℓ)

main = run {0ℓ} (putStrLn (Data.Nat.Show.show 10))
