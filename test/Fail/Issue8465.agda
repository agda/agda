-- Andreas, 2026-03-13, issue #8465
-- Definition site of a renamed thing should be the site of the renaming.
-- This used to not work properly for builtins.

module Issue8465 where

open import Issue8465.Lib

postulate
  ℕ : Set  -- Clashing with import

-- Expected error: [ClashingDefinition]
-- Multiple definitions of ℕ. Previous definition
-- ℕ is in scope as
--   * a data type Agda.Builtin.Nat.Nat brought into scope by
--     - the opening of Issue8465.Lib at << THIS FILE, ABOVE >>
--     - the opening of Agda.Builtin.Nat at << THE IMPORTED FILE, `open public` >>
--     - its definition at << THE IMPORTED FILE, `renaming` CLAUSE >>
-- when scope checking the declaration
--   ℕ : Set
