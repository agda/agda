
-- Currently modules are not allowed in mutual blocks.
-- This might change.
module ModuleInMutual where

mutual
  module A where
    T : Set -> Set
    T A = A

  module B where
    U : Set -> Set
    U B = B

