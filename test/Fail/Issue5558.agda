-- Andreas, 2021-09-14, issue #5558 reported by fgaz
-- A data definition without signature in a interleaved mutual block
-- was deemed IMPOSSIBLE, but it isn't.

interleaved mutual
  -- we don't do `data A : Set`
  data A where
    -- you don't have to actually define any constructor to trigger the error, the "where" is enough

-- Expected error:
-- Missing data signature for A
