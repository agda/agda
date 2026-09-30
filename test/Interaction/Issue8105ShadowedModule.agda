-- Andreas, 2025-09-15, issue #8105
-- Highlight module a clashing module clashes with.

module Issue8105ShadowedModule where

module M where -- This shadowed module should be highlighted as well, e.g. deadcode.

module M where -- This clashing module gets error highlighting.

-- Expected error: 8.8-9: error: [ShadowedModule]
-- Duplicate definition of module M. Previous definition of module M
-- at 6.8-9
-- when scope checking the declaration
--   module M where
