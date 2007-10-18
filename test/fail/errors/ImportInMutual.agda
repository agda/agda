
-- Currently imports are not allowed in mutual blocks.
-- This might change.
module ImportInMutual where

mutual
  import Fake.Module
  T : Set -> Set
  T A = A

