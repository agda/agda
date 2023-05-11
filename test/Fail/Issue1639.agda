-- Andreas, 2015-09-07  Issue reported by identicalsnowflake

data D : Set1 where
  field
    A : Set

-- WAS: Internal error (on master)

-- NOW:
-- A data definition can only contain type signatures, possibly under
-- keyword instance
