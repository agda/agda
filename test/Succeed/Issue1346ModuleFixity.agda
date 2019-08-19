-- Andreas, 2019-08-18, issue #1346

-- Allow fixity in renaming directive, but not for modules.

module _ where

open import Agda.Builtin.Equality using ()
  renaming (module _≡_ to infix 4 _~_)

-- Expected warning:

-- Modules do not have fixity
-- when scope checking the declaration
--   open import Agda.Builtin.Equality
--     using ()
--     renaming (module _≡_ to infix 4 _~_)
