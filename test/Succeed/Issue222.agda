
-- There were some serious bugs in the termination checker
-- which were hidden by the fact that it didn't go inside
-- records. They should be fixed now.
module Issue222 where

record R (A : Set) : Set where
  module M (a : A) where

-- Bug.agda:4,17-18
-- Panic: unbound variable A
-- when checking that the expression A has type _5
