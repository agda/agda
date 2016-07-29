-- Andreas, 2016-07-28, issue #1720

record Foo (A : Set) : Set where
  a : A
  a = {!!} where
    a' : A
    a' = {!!}

  field
    f : A

-- Now: better error:

-- This declaration is illegal in a record before the last field
-- when scope checking the declaration
--   record Foo A where
--     mutual
--       a : A
--       a = ?
--         where
--           a' : A
--           a' = ?
--     field f : A

-- Ideally: should pass
