-- This is not valid with magic mutual blocks that guess how far down the
-- file the mutual block extends
data _ where
  zero : Nat
  suc : Nat → Nat
