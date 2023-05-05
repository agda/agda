-- Andreas, 2022-10-28, issue #6244
-- Option --no-load-primitives was decided tonot be --safe.

{-# OPTIONS --no-load-primitives --safe #-}

-- Expected error:
-- Cannot set OPTIONS pragma --no-load-primitives with safe flag.
