-- Andreas, 2024-08-12
-- Test parsing REWRITE pragma with pattern synonym

data D : Set where
  c : D

pattern p = c

{-# REWRITE p #-}

-- Was: internal error
-- Expected error:
-- REWRITE used on pattern synonym
