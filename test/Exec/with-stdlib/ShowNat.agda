module ShowNat where

open import IO
open import Data.Unit
open import Data.Nat.Show

main = run (putStrLn (Data.Nat.Show.show 10))
