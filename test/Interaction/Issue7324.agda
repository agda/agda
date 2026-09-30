-- Andreas, AIM XL, 2025-05-27, issue #7324
-- Reported and test case by Naim

module Issue7324 where

open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

macro
  -- The problem was that here mymacro was highlighted in Function color.
  my-macro : Term → TC ⊤
  my-macro h = unify h (quoteTerm tt)

_ = my-macro  -- This was correctly highlighted in Macro color already.

-- Should succeed and highlight my-macro in Macro color everywhere.
