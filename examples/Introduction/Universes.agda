
module Introduction.Universes where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

postulate IsEven : Nat -> Prop

data Even : Set where
  even : (n : Nat) -> IsEven n -> Even

