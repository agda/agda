-- Andreas, 2019-07-09, issue #3900
-- Regression introduced by the fix of #3434

-- {-# OPTIONS -v tc.inj:100 #-}

data Bool : Set where
  true false : Bool

abstract

  data Unit : Set where
    unit : Unit

  f : Unit
  f with true
  ... | true  = unit
  ... | false = unit

-- Error WAS:
-- Not in Scope: unit

-- Should succeed.
