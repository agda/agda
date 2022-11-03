-- Currently open public is not allowed in erased modules. (If it were
-- allowed, then the re-exported definitions should arguably be
-- erased.)

module _ where

module @0 Bool where

  open import Agda.Builtin.Bool public

true : Bool.Bool
true = Bool.true
