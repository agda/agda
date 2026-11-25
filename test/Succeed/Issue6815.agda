-- Andreas, 2026-11-25, issue #6815 reported by Martin Escardo
-- This reproducer is by Szumi Xie from 2023-09-02.
-- The error was "Variable generalization failed" up to 2.8.0.
-- The issue is not reproducible in 2.9.0.

{-# OPTIONS --double-check #-}

-- {-# OPTIONS -v tc:20 #-}
-- {-# OPTIONS -v tc.meta.check:30 #-}
-- {-# OPTIONS -v tc.meta.assign:10 #-}
-- {-# OPTIONS -v tc.generalize:80 #-}

open import Agda.Primitive

-- data needed, error vanishes when replaced by postulates
data D : Set where
  c : D

record R (i : Level) (X : Set) : Set (lsuc i)  where
  field
    F : X → Set i
open R {{...}}

postulate
  FD : D → Set

instance
  RD : R _ D
  F {{RD}} = FD

postulate
  Fc : F c

variable
  i : Level

postulate
  g : (P : (d : D) (f : F d) → Set i)
    → P c Fc
    → (d : D)
    → (f : F d)
    → P d f

-- Error was:
-- Variable generalization failed.
--   - Probable cause
--       There were unsolved constraints that obscured the dependencies
--       between the generalized variables.
--   - Suggestion
--       The most reliable solution is to provide enough information to make
--       the dependencies clear, but simply mentioning the variables in the
--       right order should also work.
--   - Further information
--     - Dependency analysis suggested this (likely incorrect) order: i
--     - The dependency error is
--       error: [UnequalSorts]
--       (Set _i_25) != (Set (_i_31 (d = d)))

-- Should succeed.
