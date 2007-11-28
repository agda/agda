
-- Records are not allowed in mutual blocks.
module RecordInMutual where

mutual
  record A : Set where
    field x : B
  record B : Set where
    field x : A

