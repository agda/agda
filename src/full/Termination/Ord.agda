module Ord where

data Nat : Set where
  Z : Nat
  S : Nat -> Nat


data Ord : Set  where
  z : Ord
  lim : (Nat -> Ord) -> Ord

zp  : Ord -> Ord
zp z = z
zp (lim f) = lim (\x -> zp (f x))

