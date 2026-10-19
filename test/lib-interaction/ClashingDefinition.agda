-- Andreas, 2025-10-23
-- Serialize Ranges in WhyInScope data so that we have them
-- for the ClashingDefinition error.

open import Data.Nat.Base

postulate
  ℕ : Set

-- Expected error: [ClashingDefinition]
-- Multiple definitions of ℕ. Previous definition
-- ℕ is in scope as
--   * a data type Agda.Builtin.Nat.Nat brought into scope by
--     - the opening of Data.Nat.Base at <<RANGE>>
--     - the opening of Agda.Builtin.Nat at <<RANGE>>
--     - its definition at <<RANGE>>
-- when scope checking the declaration
--   ℕ : Set
--
-- <<RANGE>> should be present everywhere
