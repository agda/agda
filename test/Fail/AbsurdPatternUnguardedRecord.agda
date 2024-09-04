-- Andreas, 2024-09-04
-- Refuse directive eta-equality for unguarded records
-- Re: https://github.com/agda/agda/issues/7467#issuecomment-2326548333

-- {-# OPTIONS -v tc.pos.record:5 #-}

data ⊥ : Set where

record R : Set where
  eta-equality
  inductive
  field f : R

f : R → ⊥
f ()

-- WAS: Agda loops in type emptiness check
--
-- Expected:
