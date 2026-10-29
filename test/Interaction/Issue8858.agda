module Issue8858 where

record R : Set₁ where
  field
    foo : Set
    bar : Set

r : R
r = {!   !}

data A : Set where
  con : A → A → A

data B : Set where
  con : B

f : A → A → A
f x y = {! con x y !}

-- KEEP COMMENTS AT THE END to not mess with the ranges in Issue8858.sh

-- Issue #8858: Give and Refine left behind entries in stDisambiguatedNames
-- whose ranges point into the old goal.  A subsequent Cmd_highlight of
-- the filled-in expression then emitted these stale (shifted) annotations.

-- Expected: Cmd_highlight after give only highlights con, x, y correctly
-- and after refine only foo and bar.
