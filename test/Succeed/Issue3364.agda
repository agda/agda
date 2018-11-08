-- Andreas, 2018-11-03, issue #3364
--
-- Better error when trying to import with new qualified module name.

open import Agda.Builtin.Nat as Builtin.Nat

-- WAS: Error:
-- Not in scope:
--   as at ...
-- when scope checking as

-- NOW: Warning
-- `as' must be followed by an unqualified name
-- when scope checking the declaration
--   open import Agda.Builtin.Nat as Builtin.Nat
