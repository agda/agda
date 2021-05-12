{-# OPTIONS --guardedness #-}

module DivMod where

open import IO
open import Data.Nat
open import Data.Nat.DivMod
open import Codata.Musical.Notation
open import Data.String.Base
open import Data.Fin.Base using (toℕ)
open import Level using (0ℓ)

g : ℕ
g = 7 div 5

k : ℕ
k = toℕ (7 mod 5)

showNat : ℕ → String
showNat zero = "Z"
showNat (suc x) = "S (" ++ showNat x ++ ")"

main = run {0ℓ} (putStrLn (showNat g) >> putStrLn (showNat k))
