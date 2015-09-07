-- Andreas, 2015-09-07  Issue reported by identicalsnowflake

data D : Set1 where
  field
    A : Set

-- WAS: Internal error (on master)

-- NOW:
-- Illegal declaration in data type definition
--   field A : Set
-- when scope checking the declaration
--   data D where
--     field A : Set
