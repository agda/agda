-- Andreas, 2016-07-27, issue #2117 reported by Guillermo Calderon

-- {-# OPTIONS -v tc:10 #-}

record R : Set₁ where
  field
    A : Set

open R {{...}}

record S (r : R) : Set where
  instance i = r
  field f : A

-- ERROR WAS:
-- No instance of type R was found in scope.
-- when checking that the expression A has type Set

-- Should succeed!
