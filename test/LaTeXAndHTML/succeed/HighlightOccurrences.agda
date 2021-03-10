data Nat : Set where
  nohana : Nat
  kibou  : Nat -> Nat

one = kibou nohana
two = kibou one
