-- Andreas, 2017-10-19, issue #2808
-- The fix of #1077 was not general enough.

-- module _ where  -- If this is added, we get the error about duplicate module

postulate A : Set  -- Accepted if this is deleted

module Issue2808 where

record Issue2808 : Set where

-- Expected error: (at the postulate)
-- Illegal declaration(s) before top-level module

-- We now raise this error if the first module of the file
-- has the same name as the inferred top-level module.
