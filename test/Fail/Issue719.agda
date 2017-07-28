-- Andreas, 2012-10-19 issue #719 blame correct module
-- Andreas, 2017-07-28 point to correct binding site ("as A")

module Issue719 where

  import Common.Size as A
  module M where

  private open module A = M

-- WAS:
-- Duplicate definition of module A. Previous definition of module A
-- at .../Common/Size.agda:7,15-19
-- when scope checking the declaration
--   open module A = M

-- EXPECTED:
-- Duplicate definition of module A. Previous definition of module A
-- at .../Issue719.agda:6,25-26
-- when scope checking the declaration
--   open module A = M
