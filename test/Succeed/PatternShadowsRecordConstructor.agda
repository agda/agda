-- Andreas, 2023-09-08, issue #6829
-- The "pattern variable shadow constructor" alert should not be raised
-- for record constructors that do not allow pattern matching.

module PatternShadowsRecordConstructor where

module A where

  record B : Set where
    constructor x; no-eta-equality -- no 'pattern' directive here!

  data C : Set where
    c : B → C

open A using (C; c)

f : C → C
f (c x) = c x

-- Should succeed without warning.
