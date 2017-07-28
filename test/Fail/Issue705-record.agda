-- Andreas, 2017-07-27

module _ where

module A where
  record A : Set where

open A

open A

-- ERROR WAS:
-- Ambiguous module name A. It could refer to any one of
--   A.A
--   Issue705.A

-- EXPECTED:
-- Ambiguous module name A. It could refer to any one of
--   A.A (record module)
--   Issue705.A
