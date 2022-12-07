-- If an erased module is opened "publicly", then the re-exported
-- definitions are erased.

{-# OPTIONS --erasure #-}

import Agda.Builtin.Bool
open module @0 B = Agda.Builtin.Bool public

_ : Bool
_ = true
