-- Currently open public is not allowed in erased modules.

module _ where

import Agda.Builtin.Bool

module @0 Bool where

  open module M (_ : Set) = Agda.Builtin.Bool public
