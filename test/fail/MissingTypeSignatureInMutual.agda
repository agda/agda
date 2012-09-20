
module MissingTypeSignatureInMutual where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

mutual
  pred zero    = zero
  pred (suc n) = n

