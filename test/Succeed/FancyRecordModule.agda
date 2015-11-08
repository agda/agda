
-- Record declarations can now contain arbitrary declarations.
-- These are included in the projection module.
module FancyRecordModule where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

record Exist {A : Set}(P : A -> Set) : Set where
  field witness : A
  x = witness
  field proof   : P x
  silly : Nat -> Nat
  silly zero = zero
  silly (suc n) = silly n

postulate
  P : Nat -> Set
  e : Exist P

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

test : Exist.silly e (suc zero) == zero
test = refl

