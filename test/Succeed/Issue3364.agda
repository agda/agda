-- Andreas, 2018-11-03, issue #3364
-- Andreas, 2019-02-23, issue #3457
--
-- Better error when trying to import with new qualified module name.

open import Agda.Builtin.Nat as Builtin.Nat

-- WAS: Error:
-- Not in scope:
--   as at ...
-- when scope checking as

-- NOW: Warning
-- `as' must be followed by an identifier; a qualified name is not allowed here
-- when scope checking the declaration
--   open import Agda.Builtin.Nat as Builtin.Nat

import Agda.Builtin.Sigma as .as

-- `as' must be followed by an identifier
-- when scope checking the declaration
--   import Agda.Builtin.Sigma as .as

import Agda.Builtin.String as _

-- `as' must be followed by an identifier; an underscore is not allowed here
-- when scope checking the declaration
--   import Agda.Builtin.String as _
