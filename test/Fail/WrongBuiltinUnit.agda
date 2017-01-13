-- Andreas, 2017-01-12, re #2386
-- Correct error message for wrong BUILTIN UNIT

data Bool : Set where
  true false : Bool

{-# BUILTIN UNIT Bool #-}

-- Error WAS:
-- The builtin UNIT must be a datatype with 1 constructors
-- when checking the pragma BUILTIN UNIT Bool

-- Expected error:
-- Builtin UNIT must be a singleton record type
-- when checking the pragma BUILTIN UNIT Bool
