-- Andreas, 2026-02-28, issue #8435
-- Warn when a declaration preceeds a definition

-- {-# OPTIONS -v scope.data.range:40 #-}

mutual
  data D where
  data D : Set
  record R where
  record R : Set

-- Expected warning: -W[no]DefinitionBeforeDeclaration
-- D defined before its declaration
-- when scope checking the declaration
--   data D where

-- Expected warning: -W[no]DefinitionBeforeDeclaration
-- R defined before its declaration
-- when scope checking the declaration
--   record R where
