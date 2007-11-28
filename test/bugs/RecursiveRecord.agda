-- Make the type checker loop. How can we ensure that the record is not
-- recursive?
module RecursiveRecord where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

F : Set -> Set
F _ = R
  where
    record R : Set where
      field x : F Nat

r : F Nat
r = _
