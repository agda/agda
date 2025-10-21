-- Andreas, 2025-10-21
-- For 'ClashingDefinition', give the lineage of the previous definition.

open import Imports.A

data A : Set where

-- error: [ClashingDefinition]
-- Multiple definitions of A. Previous definition
-- A is in scope as
--   * a postulate Imports.A.A brought into scope by
--     - the opening of Imports.A at ClashingDefinitionWhyInScope.agda:4.13-22
--     - its definition at Imports/A.agda:4.11-12
-- when scope checking the declaration
--   data A : Set
