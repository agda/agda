
-- Records are allowed in mutual blocks.
module RecordInMutual where

mutual
  record B : Set

  record A : Set where
    field x : B

  record B where
    field x : A

