-- ASR (2016-09-16). These tests are disabled with the UHC
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

NaN : Float
NaN = 0.0 / 0.0

Inf : Float
Inf = 1.0 / 0.0

pi : Float
pi = 3.141592653589793

isZero : Float → String
isZero 0.0  = "pos"
isZero -0.0 = "neg"
isZero _    = "nonzero"

main : IO Unit
main =
  -- See Issues #1856 and #1857.
  putStr "√2 = " ,, print (primFloatSqrt 2.0) ,,
  putStr "√2 = " ,, print (primFloatTimes 2.0 (primSin (primFloatDiv pi 4.0))) ,,

  -- Issue #2216
  putStr "isZero  0.0 = " ,, putStrLn (isZero 0.0) ,,
  putStr "isZero -0.0 = " ,, putStrLn (isZero -0.0) ,,
  putStr "isZero  1.0 = " ,, putStrLn (isZero 1.0) ,,

  -- See Issue #1856.
  putStr "e = " ,, print (primExp 1.0) ,,
  return unit
