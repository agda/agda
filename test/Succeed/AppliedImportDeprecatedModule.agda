-- Andreas, 2024-03-29:
-- Too large range when importing and instantiating deprecated module.

open import Deprecated.Deprecated Set

postulate
  A : Set

-- Problem: Warning has too large range, spanning the rest of the file.
-- 4,1-7,10
-- warning: -W[no]UserWarning
-- Deprecated module
-- when scope checking the declaration
--   import Deprecated.Deprecated as .#Deprecated.Deprecated-8769433924480517024
