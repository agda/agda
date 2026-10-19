-- Test importing a module with a solved interaction point.
-- See Issue1296 for the same with an unsolved one.

module Issue1296 where

open import Issue1296.SolvedMeta

-- Expected error:
-- error: [SolvedButOpenHoles]
-- Issue1296.SolvedMeta (at Issue1296/SolvedMeta.agda:1.1)
-- cannot be imported since it has open interaction points
-- (consider adding {-# OPTIONS --allow-unsolved-metas #-} to that module)
-- when scope checking the declaration
--   open import Issue1296.SolvedMeta
