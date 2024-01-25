-- Testing generalized arguments
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.Generalized where

data Nat : Set where
  zeroo : Nat
  succ  : Nat → Nat


private
  variable
    m n : Nat

data Fin : Nat → Set where
  zero : Fin (succ n)
  suc  : (i : Fin n) → Fin (succ n)

toNat : (Fin n) → Nat
toNat zero    = zeroo
toNat (suc i) = succ (toNat i)
