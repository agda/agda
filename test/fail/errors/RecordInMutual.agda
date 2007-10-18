
-- Records are not allowed in mutual blocks.
module RecordInMutual where

mutual
  record A : Set where
    x : B
  record B : Set where
    x : A

