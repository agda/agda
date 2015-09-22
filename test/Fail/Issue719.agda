module Issue719 where

  import Common.Size as A
  module M where

  private open module A = M

-- NOT NICE:
-- Duplicate definition of module A. Previous definition of module A
-- at /Users/abel/cover/alfa/Agda2-clean/test/Common/Size.agda:7,15-19
-- when scope checking the declaration
--   open module A = M
