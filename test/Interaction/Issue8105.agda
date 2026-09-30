-- Andreas, 2025-09-15, issue #8105
-- Highlight definition a clashing definition clashes with

module Issue8105 where

foo -- This shadowed definition should be highlighted as well, e.g. deadcode.

data Bar : Set where
  foo : Bar  -- This clashing definition gets error highlighting.

-- Expected error: Issue8105.agda:9.3-12: error: [ClashingDefinition]
-- Multiple definitions of foo. Previous definition at
-- Issue8105.agda:6.1-4
-- when scope checking the declaration
--   foo : Bar
