-- {-# OPTIONS --compile --ghc-flag=-i.. #-}
module Issue727 where

open import Common.Prelude renaming (Nat to ℕ)
open import Common.MAlonzo hiding (main)

Sum : ℕ → Set
Sum 0       = ℕ
Sum (suc n) = ℕ → Sum n

sum : (n : ℕ) → ℕ → Sum n
sum 0       acc   = acc
sum (suc n) acc m = sum n (m + acc)

main = mainPrintNat (sum 3 0 1 2 3)
