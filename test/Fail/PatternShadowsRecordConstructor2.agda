-- Andreas, 2023-09-08, issue #6829
-- The "pattern variable shadow constructor" alert should also be raised
-- for pattern record constructors.

module PatternShadowsRecordConstructor2 where

module A where

  record B : Set where
    constructor x

  data C : Set where
    c : B → C

open A using (C; c)

f : C → C
f (c x) = c x

-- Expected alert:
--
-- The pattern variable x has the same name as the constructor A.x
-- when checking the clause left hand side
-- f (c x)
