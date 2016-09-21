-- ASR (2016-09-20). This test is disabled with the JS and UHC
-- backends. After fixing to merge it into the `Floats` tests.

module _ where

open import Common.Prelude

printB : Bool → IO Unit
printB true  = putStrLn "true"
printB false = putStrLn "false"

_/_  = primFloatDiv
_==_ = primFloatEquality

NaN : Float
NaN = 0.0 / 0.0

main : IO Unit
main =
  putStr "NaN == -NaN = " ,, printB (NaN == (primFloatNegate NaN)) ,,
  return unit
