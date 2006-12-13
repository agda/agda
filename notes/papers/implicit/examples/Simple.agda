
module Simple where

postulate
  Nat  : Set
  zero : Nat

  -- we want
  -- ?0 zero = zero
  -- and then
  -- ?0 x = x

