module Common.FFI where

type Level = Nat
data Nat = Zero | Suc Nat

fromNat :: Nat -> Integer
fromNat Zero    = 0
fromNat (Suc l) = 1 + fromNat l

instance Show Nat where
  show l = show (fromNat l)
