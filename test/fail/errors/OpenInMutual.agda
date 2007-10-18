
-- Currently open declarations are not allowed in mutual blocks.
-- This might change.
module OpenInMutual where

module A where

mutual
  open A
  T : Set -> Set
  T A = A

