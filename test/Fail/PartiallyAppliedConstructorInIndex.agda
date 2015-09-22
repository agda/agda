-- Andreas, 2015-05-02
-- To fix Issue 1497, I sacrificed this formerly passing test.
-- Which is rather far-fetched anyway: Relying on disunification
-- of higher-order indices.

module PartiallyAppliedConstructorInIndex where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat
  plus : Nat -> Nat -> Nat

data D : (Nat -> Nat) -> Set where
  c : D suc
  d : (x : Nat) -> D (plus x)
  e : D (\ x -> suc x)

f : D suc -> Nat
f c = zero
f e = suc zero
