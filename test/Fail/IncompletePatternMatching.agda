
module IncompletePatternMatching where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data True : Set where
  tt : True

data False : Set where

_==_ : Nat -> Nat -> Set
zero  == zero  = True
suc n == suc m = n == m

thm : zero == suc zero
thm = tt

