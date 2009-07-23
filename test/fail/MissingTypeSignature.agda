
module MissingTypeSignature where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

pred zero    = zero
pred (suc n) = n

