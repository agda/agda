-- Andreas, 2023-12-21, issue #7034 reported and testcase by Christian Sattler
--
-- A meta that was designated as blocker for a constraint gets instantiated by pruning here.
-- Solved by recomputing the blocker just in time.

{-# OPTIONS --two-level #-}

module Issue7034 where

open import Agda.Primitive using (SSet)

postulate
  A : SSet
  x : A

foo : {!(y : A) → ?!}  -- give "(y : A) → ?" here
foo = x

-- WAS: internal error: an instantiated meta used as blocker for a constraint.

-- Expected error:
--
-- (y : A) → ?1 (y = y) != A of type SSet
-- when checking that the expression (y : A) → ? has type SSet
