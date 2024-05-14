-- Andreas, 2024-03-01, issue #7158
-- reported and test case by Amy.
--
-- Regression in 2.5.4 concerning error message
-- given when non-function is applied.

-- {-# OPTIONS -v tc.term.args:30 #-}

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

record T : Set where
  field
    f : Nat → Nat

foo : T
foo .T.f = suc

test : Nat
test = foo zero

-- Wrong error (since Agda 2.5.4)
--
-- T !=< Nat of type Set
-- when checking that the inferred type of an application
--   T
-- matches the expected type
--   Nat
--
-- Expected error (given until Agda 2.5.3):
--
-- T should be a function type, but it isn't
-- when checking that zero is a valid argument to a function of type T
