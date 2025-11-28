-- Andreas, 2025-11-15, continue #4435
-- Better error also for record definitions with sort given
-- (same better error for data definitions was added for #4435 already).

module Issue4435-record where

-- Declarations.
record Foo (a : Set) : Set
Bar : {a : Set} → Foo a → Set₁

-- Definitions.
record Foo a : Set where
  constructor foo

Bar foo = Set


-- Expected error 1: [ClashingDefinition]
-- Multiple definitions of Foo. Previous definition
-- Foo is in scope as
--   * a postulate Issue4435-record.Foo brought into scope by
--     - its definition at ...
-- Perhaps you meant to write
--   'record Foo a where'
-- at ...?
-- In record definitions separate from their record declaration, the
-- ':' and type must be omitted
-- when scope checking the declaration
--   record Foo a : Set

-- Expected error 2: [MissingDefinitions]
-- The following names are declared but not accompanied by a
-- definition: Foo
