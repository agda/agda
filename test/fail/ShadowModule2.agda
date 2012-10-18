-- {-# OPTIONS -v scope.clash:20 #-}
-- Andreas, 2012-10-19 test case for Issue 719
module ShadowModule2 where

open import Common.Size as YesDuplicate
import Common.Size as NotDuplicate

private open module YesDuplicate = NotDuplicate
-- should report:
-- Duplicate definition of module YesDuplicate.
-- NOT: Duplicate definition of module NotDuplicate.
