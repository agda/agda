-- Andreas, 2011-10-03
{-# OPTIONS --experimental-irrelevance #-}
module MatchOnIrrelevantData1 where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

-- the index does not determine the constructor

data Fin : Nat -> Set where
  zero : (n : Nat) -> Fin (suc n)
  suc  : (n : Nat) -> Fin n -> Fin (suc n)

-- should fail:
toNat : (n : Nat) → .(Fin n) -> Nat
toNat (suc n) (zero .n) = zero
toNat (suc n) (suc .n i) = suc (toNat n i)

-- Cannot split on argument of irrelevant datatype Fin (suc @0)
-- when checking the definition of toNat
