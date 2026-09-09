
-- Tests compilation of catch-all cases
-- for data types with COMPILE pragmas

open import Agda.Builtin.Bool

open import Common.IO
open import Common.Unit

_||_ : Bool → Bool → Bool
false || false = false
_     || _      = true

main : IO Unit
main = printBool (true || false)
