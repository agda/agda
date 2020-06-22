-- Andreas, 2017-10-09, issue #2576
-- Duplicate definition should be reported as such,
-- not as "Missing type signature."

data ⊥ : Set where
data ⊥ where

-- Error was: Missing type signature for ⊥
-- Error was: Duplicate definition of module ⊥ (fixed 2019-07-07)

-- Expected error: Multiple definitions of ⊥
