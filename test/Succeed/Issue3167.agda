-- Andreas, 2018-09-12, issue #3167
--
-- If --no-prop, then Set0 is the least sort and sort constraints
-- s <= Set0 should be solved by s = Set0.

{-# OPTIONS --no-prop #-}

-- (A : Set) can be inferred if Set0 is the bottom universe

data Wrap A : Set where
  wrap : A → Wrap A

-- Should succeed with --no-prop
