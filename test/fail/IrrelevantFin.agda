-- Andreas, 2011-04-07

module IrrelevantFin where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Fin : Nat -> Set where
  zero : .(n : Nat) -> Fin (suc n)
  suc  : .(n : Nat) -> Fin n -> Fin (suc n)
-- this should not type check, since irrelevant n cannot appear in Fin n
-- or Fin (suc c)
-- note: this is possible in ICC*, but not in Agda!