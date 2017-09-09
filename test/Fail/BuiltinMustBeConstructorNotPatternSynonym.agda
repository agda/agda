-- Andreas, 2017-09-09
-- Don't allow pattern synonyms where builtin constructor is expected

data Bool : Set where
  true  : Bool
  false : Bool

pattern You = false

{-# BUILTIN BOOL  Bool #-}
{-# BUILTIN TRUE  true #-}
{-# BUILTIN FALSE You  #-}  -- This should be rejected.

-- Expected error: ;-)
-- You must be a constructor in the binding to builtin FALSE
-- when checking the pragma BUILTIN FALSE You
