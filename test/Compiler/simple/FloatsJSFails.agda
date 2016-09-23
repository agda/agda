-- ASR (2016-09-16). These tests are disabled with the JS
-- backend. After fixing a test to merge it into the `Floats` tests.

module _ where

open import Common.Prelude

print : Float → IO Unit
print x = putStrLn (primShowFloat x)

printB : Bool → IO Unit
printB true  = putStrLn "true"
printB false = putStrLn "false"

_/_ = primFloatDiv
_==_ = primFloatEquality
_<_ = primFloatLess

NaN : Float
NaN = 0.0 / 0.0

Inf : Float
Inf = 1.0 / 0.0

-Inf : Float
-Inf = -1.0 / 0.0

main : IO Unit
main =
  -- Issues #2169 and #2192.
  putStr "-0.0 = " ,, print -0.0  ,,

  putStr "NaN < -5.0  = " ,, printB (NaN < -5.0) ,,
  return unit
