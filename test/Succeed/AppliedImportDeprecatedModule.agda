-- Andreas, 2024-03-29:
-- Too large range when importing and instantiating deprecated module.

open import Deprecated.Deprecated Set

postulate
  A : Set

-- Problem: Warning has too large range, spanning the rest of the file.
--
-- Expected: 4.6-34:warning: -W[no]UserWarning
-- Deprecated module
-- when scope checking the declaration
--   open import Deprecated.Deprecated Set
